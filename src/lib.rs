//! This is a relatively simple library that is driven by the needs of [Lemurs] to parse desktop
//! entry files with a permissive license.
//!
//! ```rust
//! use deentry::DesktopEntry;
//!
//! let desktop_entry = r#"
//! [Desktop Entry]
//! Name=CoolApplication
//! Exec=/path/to/app
//! "#;
//!
//! let desktop_entry = DesktopEntry::try_from(desktop_entry)?;
//! # Ok::<(), deentry::LinedError<deentry::GroupParseError>>(())
//! ```
//!
//! [Lemurs]: https://github.com/coastalwhite/lemurs

use std::borrow::Cow;
use std::fmt::Display;
use std::num::ParseFloatError;
use std::ops::Range;
use std::str::Lines;

/// A Desktop Entry File
///
/// The structure that contains a `.desktop` or service file. This structure is divided into
/// groups. The groups can be accessed by calling the [`iter`], [`iter_mut`] or [`into_iter`]
/// functions. A Desktop Entry File can be parsed from a `&str` by calling the
/// [`DesktopEntry::try_from`] function.
///
/// # Examples
///
/// ## Parsing a Desktop Entry
///
/// ```rust
/// use deentry::DesktopEntry;
///
/// let desktop_entry = r#"
/// [Desktop Entry]
/// Name=CoolApplication
/// Exec=/path/to/app
/// "#;
///
/// let desktop_entry = DesktopEntry::try_from(desktop_entry)?;
/// # Ok::<(), deentry::LinedError<deentry::GroupParseError>>(())
/// ```
#[derive(Debug, Clone)]
pub struct DesktopEntry<'a> {
    groups: Vec<DesktopEntryGroup<'a>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DesktopEntryGroup<'a> {
    line_range: Range<usize>,
    group_name: &'a str,
    entries: Vec<DesktopEntryGroupEntry<'a>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct DesktopEntryGroupEntry<'a> {
    locale: Option<&'a str>,
    key: &'a str,
    value: EntryValue<'a>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct EntryValue<'a> {
    content: Cow<'a, str>,
    has_locale: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GroupParseError {
    Empty,
    NoHeader,
    HeaderError(GroupHeaderParseError),
    EntryError(EntryParseError),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GroupHeaderParseError {
    InvalidStart,
    InvalidEnd,
    NotASCII,
    ContainsBrackets,
    ContainsControlCharacters,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EntryParseError {
    Empty,
    Comment,
    Header,
    NoEquals,
    InvalidKey,
    EscapedIntoNonExistant,
    EscapedIntoHeader,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueStringError {
    HasLocale,
    NotASCII,
    ControlCharacters,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ValueBoolError {
    HasLocale,
    NotABoolean,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ValueNumericError {
    HasLocale,
    FloatParseError(ParseFloatError),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinedError<E> {
    pub line_nr: usize,
    pub error: E,
}

impl<'a> DesktopEntry<'a> {
    /// Get a slice with all the groups in the desktop entry file
    pub fn groups(&self) -> &[DesktopEntryGroup<'a>] {
        &self.groups
    }

    /// Get a mutable slice with all the groups in the desktop entry file
    pub fn groups_mut(&mut self) -> &mut [DesktopEntryGroup<'a>] {
        &mut self.groups
    }
}

impl<'a> TryFrom<&'a str> for DesktopEntry<'a> {
    type Error = LinedError<GroupParseError>;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        let mut lines = s.lines();

        let first_group = DesktopEntryGroup::from_lines(&mut lines, 0)?;

        let mut groups = Vec::new();

        let mut line_nr = first_group.line_range.end;
        groups.push(first_group);
        loop {
            match DesktopEntryGroup::from_lines(&mut lines, line_nr) {
                Ok(group) => {
                    line_nr = group.line_range.end;
                    groups.push(group);
                }
                Err(lined_err) if lined_err.error == GroupParseError::Empty => break,
                Err(err) => return Err(err),
            }
        }

        Ok(Self { groups })
    }
}

impl<'a> DesktopEntryGroup<'a> {
    /// Get the group name
    ///
    /// Example:
    ///
    /// ```
    /// [Desktop Entry]
    /// Exec=/usr/bin/cool
    /// ```
    ///
    /// Here "Desktop Entry" is the group name.
    pub fn name(&self) -> &'a str {
        self.group_name
    }

    /// Get the entry belonging to a key
    pub fn get(&self, key: &str) -> Option<&DesktopEntryGroupEntry<'a>> {
        self.entries().iter().find(|e| e.key() == key)
    }

    /// Get the entry belonging to a key
    pub fn contains(&self, key: &str) -> bool {
        self.get(key).is_some()
    }

    /// Get a slice with all the entries in the group
    pub fn entries(&self) -> &[DesktopEntryGroupEntry<'a>] {
        &self.entries
    }

    /// Get a mutable slice with all the entries in the group
    pub fn entries_mut(&mut self) -> &mut [DesktopEntryGroupEntry<'a>] {
        &mut self.entries
    }

    fn from_lines(
        lines: &mut Lines<'a>,
        line_nr: usize,
    ) -> Result<Self, LinedError<GroupParseError>> {
        let start_line_nr = line_nr;

        // Skip over blank lines
        let mut start_line = lines
            .next()
            .ok_or(GroupParseError::Empty.at_line(start_line_nr))?
            .trim_start();
        let mut current_line_nr = line_nr + 1;
        while start_line.is_empty() || start_line.starts_with('#') {
            start_line = lines
                .next()
                .ok_or(GroupParseError::Empty.at_line(current_line_nr))?
                .trim_start();
            current_line_nr += 1;
        }

        let group_header = start_line.trim_end();
        if !group_header.starts_with('[') {
            return Err(GroupParseError::NoHeader.at_line(current_line_nr));
        }

        if !group_header.ends_with(']') {
            return Err(GroupParseError::NoHeader.at_line(current_line_nr));
        }

        let group_name = group_header_from_line(group_header)
            .map_err(|err| GroupParseError::HeaderError(err).at_line(current_line_nr))?;

        let mut entries = Vec::new();
        loop {
            let mut sub_lines = lines.clone();

            if lines.clone().next().is_none() {
                break;
            }

            match DesktopEntryGroupEntry::from_lines(&mut sub_lines, &mut current_line_nr) {
                Ok(entry) => entries.push(entry),
                Err(EntryParseError::Header) => {
                    current_line_nr -= 1;
                    break;
                }
                Err(err) if err.is_empty_line() => {}
                Err(err) => return Err(GroupParseError::EntryError(err).at_line(current_line_nr)),
            }

            *lines = sub_lines;
        }

        Ok(Self {
            line_range: start_line_nr..current_line_nr,
            group_name,
            entries,
        })
    }
}

fn group_header_from_line(line: &str) -> Result<&str, GroupHeaderParseError> {
    debug_assert!(!line.contains('\n'));

    let line = line.trim();

    if !line.starts_with('[') {
        return Err(GroupHeaderParseError::InvalidStart);
    }

    if !line.ends_with(']') {
        return Err(GroupHeaderParseError::InvalidEnd);
    }

    let group_name = &line[1..line.len() - 1];

    if !group_name.is_ascii() {
        return Err(GroupHeaderParseError::NotASCII);
    }

    if group_name.contains(&['[', ']']) {
        return Err(GroupHeaderParseError::ContainsBrackets);
    }

    if group_name.contains(|c: char| c.is_ascii_control()) {
        return Err(GroupHeaderParseError::ContainsControlCharacters);
    }

    Ok(group_name)
}

impl<'a> DesktopEntryGroupEntry<'a> {
    /// Get the key for the group entry
    pub fn key(&self) -> &'a str {
        self.key
    }

    /// Get the value for the group entry
    pub fn value(&self) -> &EntryValue<'a> {
        &self.value
    }

    fn from_lines(
        lines: &mut Lines<'a>,
        current_line_nr: &mut usize,
    ) -> Result<Self, EntryParseError> {
        let line = lines.next().ok_or(EntryParseError::Empty)?;
        *current_line_nr += 1;

        if line.trim_start().is_empty() {
            return Err(EntryParseError::Empty);
        }

        if line.trim_start().starts_with('#') {
            return Err(EntryParseError::Comment);
        }

        if line.trim_start().starts_with('[') {
            return Err(EntryParseError::Header);
        }

        let Some(equals_position) = line.find('=') else {
            return Err(EntryParseError::NoEquals);
        };

        let key = &line[..equals_position];
        let value = &line[equals_position + 1..];

        // "Space before and after the equals sign should be ignored"
        let key = key.trim_end();
        let value = value.trim_start();

        // Parse the locale string
        let (key, locale) = if key.ends_with(']') {
            let Some(locale_start) = key.find('[') else {
                return Err(EntryParseError::InvalidKey);
            };

            (
                key[..locale_start].trim_end(),
                Some(&key[locale_start + 1..key.len() - 1]),
            )
        } else {
            (key, None)
        };

        let category_length = if let Some(category_length) = key.find('/') {
            if !key[category_length + 1..].is_ascii() {
                return Err(EntryParseError::InvalidKey);
            }

            category_length
        } else {
            key.len()
        };

        if key[..category_length].contains(|c: char| !c.is_ascii_alphanumeric() && c != '-') {
            return Err(EntryParseError::InvalidKey);
        }

        // Extend line if it ends with a '\'
        if !value.ends_with('\\') {
            let value = EntryValue {
                content: Cow::Borrowed(value),
                has_locale: locale.is_some(),
            };

            return Ok(Self { locale, key, value });
        }

        let mut value = String::from(value);
        while value.ends_with('\\') {
            let line = lines
                .next()
                .ok_or(EntryParseError::EscapedIntoNonExistant)?;
            *current_line_nr += 1;

            if line.starts_with('[') {
                return Err(EntryParseError::EscapedIntoHeader);
            }

            value.pop(); // Removes '\'
            value.push(' ');
            value.push_str(line.trim_start());
        }

        let value = EntryValue {
            content: Cow::Owned(value),
            has_locale: locale.is_some(),
        };

        Ok(Self { locale, key, value })
    }
}

impl<'a> EntryValue<'a> {
    /// Try to regard the entry value as a boolean
    pub fn as_boolean(self) -> Result<bool, ValueBoolError> {
        if self.has_locale {
            return Err(ValueBoolError::HasLocale);
        }

        match self.content.trim() {
            "true" => Ok(true),
            "false" => Ok(false),
            _ => Err(ValueBoolError::NotABoolean),
        }
    }

    /// Try to regard the entry value as a numeric value
    pub fn as_numeric(self) -> Result<f32, ValueNumericError> {
        if self.has_locale {
            return Err(ValueNumericError::HasLocale);
        }

        // NOTE: this might not be 100% correct as '%f' in scanf in C might be different.
        self.content
            .trim()
            .parse()
            .map_err(|err| ValueNumericError::FloatParseError(err))
    }

    /// Try to regard the entry value as a string
    pub fn as_string(&'a self) -> Result<&'a str, ValueStringError> {
        if self.has_locale {
            return Err(ValueStringError::HasLocale);
        }

        let line = self.content.trim();

        if !line.is_ascii() {
            return Err(ValueStringError::NotASCII);
        }

        if line.contains(|c: char| c.is_ascii_control()) {
            return Err(ValueStringError::ControlCharacters);
        }

        Ok(&line)
    }

    /// Try to regard the entry value as a locale string
    pub fn as_localestring(&'a self) -> &'a str {
        &self.content.trim()
    }
}

impl GroupParseError {
    pub fn at_line(self, line_nr: usize) -> LinedError<Self> {
        LinedError {
            line_nr,
            error: self,
        }
    }
}

impl Display for GroupParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use GroupParseError::*;

        f.write_str("DesktopEntry failed to parse. ")?;

        match self {
            Empty => f.write_str("String is empty."),
            NoHeader => f.write_str("String does not contain Group Header."),
            HeaderError(err) => write!(f, "Invalid Group Header. Reason: {err}."),
            EntryError(err) => write!(f, "Invalid Entry pair. Reason: {err}."),
        }
    }
}

impl std::error::Error for GroupParseError {}

impl GroupHeaderParseError {
    pub fn at_line(self, line_nr: usize) -> LinedError<Self> {
        LinedError {
            line_nr,
            error: self,
        }
    }
}

impl Display for GroupHeaderParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use GroupHeaderParseError::*;

        match self {
            InvalidStart => f.write_str("Line does not start with '['"),
            InvalidEnd => f.write_str("Line does not end with ']'"),
            NotASCII => f.write_str("Group Name does not consist of ASCII"),
            ContainsBrackets => f.write_str("Group Name contains brackets"),
            ContainsControlCharacters => {
                f.write_str("Group Name contains ASCII control characters")
            }
        }
    }
}

impl std::error::Error for GroupHeaderParseError {}

impl EntryParseError {
    fn is_empty_line(self) -> bool {
        use EntryParseError::*;
        matches!(self, Empty | Comment)
    }

    pub fn at_line(self, line_nr: usize) -> LinedError<Self> {
        LinedError {
            line_nr,
            error: self,
        }
    }
}

impl Display for EntryParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use EntryParseError::*;

        match self {
            Empty => f.write_str("Line is empty."),
            Comment => f.write_str("Line contains a comment."),
            Header => f.write_str("Line contains a Group Header."),
            NoEquals => f.write_str("Line does not contain a '='."),
            InvalidKey => f.write_str("Entry Key contains invalid characters."),
            EscapedIntoNonExistant => {
                f.write_str("Entry Value escapes end of line, but there is no next line")
            }
            EscapedIntoHeader => {
                f.write_str("Entry Value escapes end of line, but next line is a header")
            }
        }
    }
}

impl std::error::Error for EntryParseError {}

impl Display for ValueStringError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use ValueStringError as E;

        f.write_str(match self {
            E::HasLocale => "Value cannot be converted into a string, because it has a locale",
            E::NotASCII => "Value cannot be converted into a string, because it is not valid ASCII",
            E::ControlCharacters => {
                "Value cannot be converted into a string, because it contains control characters"
            }
        })
    }
}

impl std::error::Error for ValueStringError {}

impl Display for ValueBoolError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use ValueBoolError as E;

        f.write_str(match self {
            E::HasLocale => "Value cannot be converted into a boolean, because it has a locale",
            E::NotABoolean => {
                "Value cannot be converted into a boolean, because it is not 'true' or 'false'"
            }
        })
    }
}

impl std::error::Error for ValueBoolError {}

impl Display for ValueNumericError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use ValueNumericError as E;

        match self {
            E::HasLocale => f.write_str("Value cannot be converted into a numeric value, because it has a locale"),
            E::FloatParseError(err) => write!(f, "Value cannot be converted into a numeric value, because it could not be parsed. Reason: '{err}'"),
        }
    }
}

impl std::error::Error for ValueNumericError {}

impl<E: std::fmt::Display> std::fmt::Display for LinedError<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let LinedError { line_nr, error } = self;

        write!(f, "Line {line_nr}: {error}")
    }
}
impl<E: std::error::Error> std::error::Error for LinedError<E> {}

#[cfg(test)]
mod tests {
    use std::env;
    use std::path::Path;

    use regex::Regex;

    use super::*;

    #[test]
    fn desktop_entry_group_entry_from_line() {
        macro_rules! assert_entry_eq {
            ($lines:literal => $key:literal, $value:literal $(, $locale:literal)? $(,)?) => {
                let mut lines = $lines.lines();
                let entry = DesktopEntryGroupEntry::from_lines(&mut lines, &mut 0);
                assert!(entry.is_ok(), "Entry formed from '{}' is Err", $lines);
                let entry = entry.unwrap();
                assert_eq!(&entry.key, &$key);
                assert_eq!(&entry.value.content, &$value);
                #[allow(unused)]
                let locale: Option<&str> = None;
                $(
                let locale = Some($locale);
                )?
                assert_eq!(entry.locale, locale);
            };
            ($lines:literal => ! $err:ident) => {
                let mut lines = $lines.lines();
                let entry = DesktopEntryGroupEntry::from_lines(&mut lines, &mut 0);
                assert!(entry.is_err(), "Entry formed from '{}' is Ok", $lines);
                let entry = entry.unwrap_err();
                assert_eq!(entry, <EntryParseError>::$err);
            };
        }

        assert_entry_eq!("" => ! Empty);
        assert_entry_eq!("   " => ! Empty);

        assert_entry_eq!("#" => ! Comment);
        assert_entry_eq!("#test" => ! Comment);
        assert_entry_eq!(" #test" => ! Comment);

        assert_entry_eq!("test" => ! NoEquals);

        assert_entry_eq!("*=" => ! InvalidKey);
        assert_entry_eq!("a*=" => ! InvalidKey);
        assert_entry_eq!("*=c" => ! InvalidKey);

        assert_entry_eq!("a=b\\" => ! EscapedIntoNonExistant);
        assert_entry_eq!("a=b\\\n[" => ! EscapedIntoHeader);

        assert_entry_eq!("a=b" => "a", "b");
        assert_entry_eq!("a=b\\\nc" => "a", "b c");
        assert_entry_eq!("a=b\\\nc\\\nd" => "a", "b c d");

        assert_entry_eq!("a = b" => "a", "b");
        assert_entry_eq!("abc=def" => "abc", "def");
        assert_entry_eq!("Exec=/usr/bin/lemurs" => "Exec", "/usr/bin/lemurs");

        assert_entry_eq!("Name[abc]=xyz" => "Name", "xyz", "abc");
    }

    #[test]
    fn grp_header_from_line() {
        macro_rules! assert_groupheader_eq {
            ($line:literal => $value:literal) => {
                let group_name = group_header_from_line($line);
                assert!(
                    group_name.is_ok(),
                    "Group header formed from '{}' is Err",
                    $line
                );
                let group_name = group_name.unwrap();
                assert_eq!(&group_name, &$value);
            };
            ($line:literal => ! $err:ident) => {
                let group_name = group_header_from_line($line);
                assert!(
                    group_name.is_err(),
                    "Group header formed from '{}' is Ok",
                    $line
                );
                let group_name = group_name.unwrap_err();
                assert_eq!(group_name, <GroupHeaderParseError>::$err);
            };
        }

        assert_groupheader_eq!("" => ! InvalidStart);
        assert_groupheader_eq!("[" => ! InvalidEnd);

        assert_groupheader_eq!("[[]" => ! ContainsBrackets);
        assert_groupheader_eq!("[]]" => ! ContainsBrackets);

        assert_groupheader_eq!("[\x07]" => ! ContainsControlCharacters);
        assert_groupheader_eq!("[\0]" => ! ContainsControlCharacters);

        assert_groupheader_eq!("[🐒]" => ! NotASCII);

        assert_groupheader_eq!("[]" => "");
        assert_groupheader_eq!("  []" => "");
        assert_groupheader_eq!("[]   " => "");

        assert_groupheader_eq!("[abc]" => "abc");
        assert_groupheader_eq!("[abc xyz]" => "abc xyz");
        assert_groupheader_eq!("[Desktop Entry]" => "Desktop Entry");
    }

    #[test]
    fn group_from_lines() {
        macro_rules! assert_group_eq {
            ($lines:literal => $name:literal, $end:literal, [$(($key:literal, $value:literal)),*] $(,)?) => {
                let mut lines = $lines.lines();
                let group = DesktopEntryGroup::from_lines(&mut lines, 0);
                assert!(group.is_ok(), "Group formed from '{}' is Err({err:?})", $lines, err = group.unwrap_err());

                let group = group.unwrap();

                assert_eq!(group.line_range.end, $end);

                let expected_entries: &[(&str, &str)] = &[$(($key, $value)),*];

                assert_eq!(expected_entries.len(), group.entries.len());

                for i in 0..expected_entries.len() {
                    // assert_eq!(expected_entries[i].0, group.entries.get(i).unwrap().1.key);
                    assert_eq!(expected_entries[i].1, group.entries.get(i).unwrap().value.content);
                }
            };
            ($lines:literal => ! $err:expr) => {
                let mut lines = $lines.lines();
                let group = DesktopEntryGroup::from_lines(&mut lines, 0);
                assert!(group.is_err(), "Group formed from '{}' is Ok", $lines);
                let group = group.unwrap_err();
                assert_eq!(group.error, $err);
            };
        }

        use GroupParseError::*;

        assert_group_eq!("" => ! Empty);
        assert_group_eq!("abc = xyz" => ! NoHeader);
        assert_group_eq!("[[]" => ! HeaderError(GroupHeaderParseError::ContainsBrackets));
        assert_group_eq!("[abc]\n*=" => ! EntryError(EntryParseError::InvalidKey));

        assert_group_eq!("[]" => "", 1, []);
        assert_group_eq!("  []" => "", 1, []);
        assert_group_eq!("[]   " => "", 1, []);

        assert_group_eq!("[abc]" => "abc", 1, []);
        assert_group_eq!("[abc xyz]" => "abc xyz", 1, []);
        assert_group_eq!("[Desktop Entry]" => "Desktop Entry", 1, []);

        assert_group_eq!(r#"
[Desktop Entry]
abc = xyz
Exec=/usr/bin/lemurs

[Other Group]
key = value
            "# => "Desktop Entry", 5, [("abc", "xyz"), ("Exec", "/usr/bin/lemurs")]
        );
    }

    #[test]
    fn file_from_lines() {
        let desktop_entry = DesktopEntry::try_from(
            r#"
[Desktop Entry]
abc = xyz
Exec=/usr/bin/lemurs

[Other Group]
key = value
            "#,
        );
        assert!(
            desktop_entry.is_ok(),
            "{err}",
            err = desktop_entry.unwrap_err()
        );
    }

    fn assert_all_files_in_directory(dir: &Path, regex: Option<&Regex>) -> u64 {
        let mut count = 0;

        assert!(dir.is_dir());

        for entry in std::fs::read_dir(dir).unwrap() {
            let entry = entry.unwrap();

            let path = entry.path();
            if path.is_dir() {
                count += assert_all_files_in_directory(&path, regex);
            } else {
                if let Some(regex) = regex {
                    if regex.is_match(&path.display().to_string()) {
                        continue;
                    }
                }

                count += 1;

                let entry_content = std::fs::read_to_string(path.clone()).unwrap();
                let desktop_entry = DesktopEntry::try_from(&entry_content[..]);

                if let Err(err) = desktop_entry {
                    println!("Error = {err}");
                    println!("Path = {}", path.display());
                    println!("Content = '''\n{entry_content}\n'''");

                    assert!(false);
                }
            }
        }

        count
    }

    #[test]
    #[ignore]
    fn parse_xsessions() {
        let path = Path::new("/usr/share/xsessions");

        if !path.exists() {
            return;
        }

        let count = assert_all_files_in_directory(path, None);
        println!("Checked {count} files");
    }

    #[test]
    #[ignore]
    fn parse_wayland_sessions() {
        let path = Path::new("/usr/share/wayland-sessions");

        if !path.exists() {
            return;
        }

        let count = assert_all_files_in_directory(path, None);
        println!("Checked {count} files");
    }

    #[test]
    #[ignore]
    fn parse_service_files() {
        let path = Path::new("/usr/lib/systemd/system");

        if !path.exists() {
            return;
        }

        let regex = Regex::new(r"\.conf$").unwrap();
        let count = assert_all_files_in_directory(path, Some(&regex));
        println!("Checked {count} files");
    }

    #[test]
    #[ignore]
    fn parse_share_application_files() {
        let path = Path::new("/usr/share/applications");

        if !path.exists() {
            return;
        }

        let regex = Regex::new(r"\.conf$").unwrap();
        let count = assert_all_files_in_directory(path, Some(&regex));
        println!("Checked {count} files");
    }

    #[test]
    #[ignore]
    fn parse_local_application_files() {
        let path = format!(
            "{home}/.local/share/applications",
            home = env::var("HOME").unwrap()
        );
        let path = Path::new(&path);

        if !path.exists() {
            return;
        }

        let regex = Regex::new(r"\.conf$").unwrap();
        let count = assert_all_files_in_directory(path, Some(&regex));
        println!("Checked {count} files");
    }
}
