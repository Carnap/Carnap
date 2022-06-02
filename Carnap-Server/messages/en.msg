# templates/homepage.hamlet
HomepageWelcome: Welcome to Carnap.io
HomepageSubtitle: A formal logic framework for Haskell
HomepageHeader: Background
HomepageTextPrefix1: Carnap is a free and open software framework written in
HomepageTextLink1: Haskell
HomepageTextSuffix1: for teaching and studying formal logic. 
HomepageTextPrefix2: Carnap powers logic courses at
HomepageTextLink2: dozens of colleges and universities
HomepageTextSuffix2: around the world.
HomepageText3: If you're a student in a course that uses Carnap, please follow the links at the top of the page to log in and to access course materials.
HomepageTextPrefix4: If you're just curious about Carnap, you can find some general information on our
HomepageTextLink4: about
HomepageTextSuffix4: page. 
HomepageTextPrefix5: If you're interested in the project, and would like to use Carnap in a class you're teaching, or get involved in some other way, please feel free to 
HomepageTextLink5: get in touch!

# templates/infopage.hamlet
InfopageAboutCarnap: About Carnap
InfopageWhatIs: What is Carnap?
InfopageWhatFor: What's Carnap for?
InfopageHowToUse: How can I use Carnap?
InfopageWhyName: Why “Carnap”?
InfopageWhoUses: Who uses Carnap?
InfopageHowWorks: How does Carnap Work?
InfopageHowHelp: How can I get involved?
InfopageCarnapQuote1: “The acceptance or rejection of abstract linguistic forms, just as the acceptance or rejection of any other linguistic forms in any branch of science, will finally be decided by their efficiency as instruments, the ratio of the results achieved to the amount and complexity of the efforts required. To decree dogmatic prohibitions of certain linguistic forms instead of testing them by their success or failure in practical use, is worse than futile; it is positively harmful because it may obstruct scientific progress.
InfopageCarnapQuote2: Let us grant to those who work in any special field of investigation the freedom to use any form of expression which seems useful to them; the work in the field will sooner or later lead to the elimination of those forms which have no useful function. Let us be cautious in making assertions and critical in examining them, but tolerant in permitting linguistic forms.”
InfopageCarnapQuoteSource: Empiricism Semantics and Ontology
InfopageWhatIsText: Carnap is a free and open-source Haskell framework for creating and exploring formal languages, logics, and semantics. It lets you quickly and straightforwardly define languages, construct logics for those languages, and stipulate their semantics. Carnap then uses your specifications to figure out how to check proofs in a variety of formal systems using your logic, how to find the meanings of compound expressions, and a whole lot more.

InfopageDemos: Demos
InfopageDemosHere: Here are some quick examples of what Carnap can do.
InfopageDemosText1: This is a proofbox with a Kalish and Montague System for Propositional Logic. You can directly manipulate the proof by typing in the proofbox, and see the effects of your changes by mousing over the line-decorations on the right hand side. 
InfopageDemosText2: This is a rendering proofbox with a Kalish and Montague System for Propositional Logic, which also visually displays the structure of the proof being developed.
InfopageDemosText3: This is a rendering proofbox with Hardegree's variation on a Montague system.
InfopageDemosTextPrefix4: This is a proofbox with a Fitch system, using rules from 
InfopageDemosTextItalics4: The Logic Book
InfopageDemosTextSuffix4: and visually rendering the proof structure in the Fitch style.
InfopageDemosText5: This is a proofbox with a Kalish and Montague System for First-Order Logic, displaying a proof of Russell's Theorem.
InfopageDemosTextPrefix6: This is a proof with Goldfarb's Lemmon-style system of natural deduction, from the textbook 
InfopageDemosTextItalics6: Deductive Logic
InfopageDemosTextSuffix6:
InfopageDemosText7: Here’s a proof of the fact that the bisectors of the sides of a triangle always meet at a point (from the assumption that a point is on the bisector of a segment if and only if it’s equidistant from the endpoints of that segment). “F(x,y)” abbreviates that “x is on y“, “g(y,z)” abbreviates “the bisector of the segment given by y and z”, and “h(x,z)” abbreviates “the distance from x to z”.
InfopageDemosText8: (Because of the number of variables, this one may take a moment to load initially. Once loaded, it should respond quickly to changes.)
InfopageDemosTextPrefix9: Here are two more proofs of Russell's theorem, this time using a version of system QL, from P.D. Magnus' free and open textbook 
InfopageDemosTextLinkA9: Forall x
InfopageDemosTextInfixA9: , and the system FOL from the 
InfopageDemosTextLinkB9: Calgary Remix
InfopageDemosTextSuffix9: of Forall x.
InfopageDemosText10: Note that we've changed how formulas are parsed (dropping the parentheses around the arguments to predicates), to match the display style of Forall x.
InfopageDemosText11: This is a proofbox with a Kalish and Montague System for Monadic Second-Order Logic, showing how to prove an instance of the comprehension scheme, using a predicate abstraction rule.
InfopageDemosText12: This is a proof that every relation has an inverse, in a system of arbitrarily (finitely) Polyadic Second-Order Logic, again making use of a predicate abstraction rule.
InfopageDemosTextPrefix13: This is a proof that the powerset of a transitive set is transitive (exercise 3, chapter 3.3 from Velleman's
InfopageDemosTextItalics13: Deductive Logic
InfopageDemosTextSuffix13: ), in a system of elementary set theory.
InfopageDemosTextPrefix14: Here are proofs of axioms 5 and B within natural deduction systems for propositional modal logics K5 and KTB, in the style of Hardegree's 
InfopageDemosTextLink14: Modal Logic
InfopageDemosTextSuffix14:
InfopageDemosTextPrefix15: These use 
InfopageDemosTextLink15: Fira Logic
InfopageDemosTextSuffix15: for nicer-looking logical symbols and use guards to help visually indicate the scope of each subproof.
InfopageDemosTextPrefix16: Here's a proof of the Barcan Formula within a naïvely quantified system of modal logic, based on the system MPL of Hardegree's
InfopageDemosTextLink16: Modal Logic
InfopageDemosTextSuffix16:
InfopageDemosTextPrefix17: Carnap supports proofs written in the sequent calculus, via 
InfopageDemosTextLink17: ProofJS
InfopageDemosTextSuffix17:
InfopageDemosText18: Among the systems supported are propositional and first order variants of Gentzen's original LK and LJ.
InfopageDemosTextPrefix19: Carnap also includes a JSON API, making it possible to create pure JavaScript GUIs that use Carnap under the hood for in-browser proof checking. Here's an example of such a GUI, adapted from 
InfopageDemosTextLink19: Keven Klement's Forall x proof checker
InfopageDemosTextSuffix19: using P.D. Magnus' Forall x system SL.
InfopageDemosText20: example 17

InfopageWhy1: What's Carnap for?
InfopageWhy2: Carnap is intended for use by educators, students, and researchers working on logic. Carnap makes it possible for educators to create interactive exercises and teaching materials, and for students to get quick and helpful feedback as they learn semantic and syntactic methods for determining what follows from what. Carnap also enables researchers interested in unorthodox formal systems to rapidly prototype proof-checking and semantic tools for computer-assisted logical investigation.

InfopageUsage1: How can I use Carnap right now?
InfopageUsage2: You can use Carnap to teach your own logic class!
InfopageUsagePrefix3: All you need to do is
InfopageUsageLinkA3: create an account 
InfopageUsageInfix3: and then 
InfopageUsageLinkB3: get in touch
InfopageUsageSuffix3: register as an instructor.
InfopageUsage4: Once you're an instructor, you can use this site—the one you're on right now, carnap.io—to run your class and automatically grade homework.
InfopageUsagePrefix5: You can either assign problems from the free
InfopageUsageLink5: textbook 
InfopageUsageSuffix5: hosted here, or you can use your own textbook and create automatically graded problem-sets for your own preferred system.
InfopageUsagePrefix6: Carnap currently supports truth-tables and translation and parsing exercises, as well as deductions compatible with formal systems used in Kalish and Montague's
InfopageUsageItalicsA6: Logic
InfopageUsageInfixA6: Bergmann and Moore's
InfopageUsageItalicsB6: Logic Book
InfopageUsageInfixB6: Hardegree's
InfopageUsageItalicsC6: Modal Logic
InfopageUsageInfixC6: P.D. Magnus'
InfopageUsageItalicsD6: Forall x
InfopageUsageInfixD6: and the Calgary Remix of
InfopageUsageItalicsE6: Forall x
InfopageUsageSuffix6:
InfopageUsage7: But the ambition of the project is maximum coverage. So if your favorite system isn't supported, let us know and we'll see about adding it.
InfopageUsagePrefix8: Documentation for potential instructors can be found
InfopageUsageLink8: here
InfopageUsageSuffix8:


InfopageName1: Why “Carnap”?
InfopageName2: Carnap is named after Rudolf Carnap, the philosopher quoted above.
InfopageName3: Carnap (the philosopher) famously advocated a tolerant and experimental approach to logic. Carnap (the program) is pluralistic by design. Inference rules are specified declaratively, making it easy to add new logics to those already provided for a given language. The algorithms for checking whether inferences are correct are applicable to a wide variety of languages, making it easy to introduce new languages.
InfopageName4: Carnap (the philosopher) also had a lot to say about logical types, and how ignoring them can leave you with beliefs that don’t work very well. Carnap (the program) is written in Haskell, a statically-typed pure functional programming language that uses a theory of logical types to ensure code correctness.

InfopageWho1: Who Uses Carnap?
InfopageWho2: Carnap was initially developed at Kansas State University, but is now used at dozens of colleges and universities around the world. Here's an (incomplete) list:

InfopageHow1: How does Carnap work?
InfopageHow2: Well, it's a little technical. There are a couple of different tricks involved.
InfopageHowPrefix3: Essentially, Haskell's type system makes it possible to represent different lexical categories as datatypes, to combine these lexical category datatypes into a larger datatype representing a lexicon (using something like the method described in
InfopageHowLink3: this paper
InfopageHowSuffix3: ), and to define a language as the result of applying different elements of a lexicon to one another in a grammatical way.
InfopageHow4: The upshot is that, using Carnap, you can define a language as the result of snapping together predefined lexical categories. Thanks to Haskell's typeclasses, your languages will inherit various useful properties that their constituent lexical categories carry along with them (for example, languages that contain the lexical category for Boolean connectives will automatically know how to parse and display the symbol for “and”, or how to compute the semantic value of a conjunction from the semantic values of its conjuncts). And, because of Haskell's static typing and the trick of representing lexical categories as types, you're guaranteed that any programming mistake potentially resulting in an ungrammatical expression will be detected when you try to compile the program.
InfopageHow5: By representing a large class of languages uniformly (as the result of snapping together lexical categories), we also end up being able to manipulate them uniformly. In particular, we can use entirely generic algorithms for things like variable substitution, semantic evaluation, β-normalization, higher-order unification… all the good stuff that you need in order to, for example, check proofs for correctness using only a declaration of acceptable inference rules. As a result, we only need to write code for these algorithms once; we can then automatically use that code with any language that can be defined in the Carnap framework.
InfopageHowPrefix6: So that's the gist of it. If you'd like to learn more about the details, you can inspect the code, talk to a developer, or take a look at 
InfopageHowLink6: this paper
InfopageHowSuffix6:

InfopageContributing1: How can I get involved?
InfopageContributingPrefix2: If you’d like to support Carnap, please consider starring us on 
InfopageContributingLink2: Github
InfopageContributingSuffix2:
InfopageContributing3: If you have suggestions, feature requests, or bug-reports, you can create an issue on Github.
InfopageContributingPrefix4: For general questions or discussion, you can also reach us on
InfopageContributingLinkA4: Matrix
InfopageContributingInfixA4: which is bridged on IRC at
InfopageContributingLinkB4: ircs://irc.libera.chat:6697/carnap
InfopageContributingInfixB4: or over
InfopageContributingLinkC4: email
InfopageContributingSuffix4:
InfopageContributing5: If you’d like to contribute some code to the project—anything from a new unification algorithm to a CSS tweak or pandoc template—just put in a pull request!

# templates/auth-layout.hamlet, templates/default-layout.hamlet
LayoutAbout: About
LayoutBook: Book
LayoutMessage: Message
LayoutUserHome: User Home
LayoutInstructorHome: Instructor Home
LayoutSharedDocuments: Shared Documents
LayoutSharedDocumentation: Documentation
LayoutLogout: Logout
LayoutLogin: Login

# templates/documentIndex.hamlet

DocumentIndexFilterByTag: Filter by Tag
DocumentIndexPubliclyShared: Publicly Shared
DocumentIndexInstructorsOnly: Instructors Only

# templates/passwordEntry.hamlet

PasswordEntryRequest: Please enter the access key for this assignment

# templates/register.hamlet

RegisterNeedTo: Looks Like You Need to Register
RegisterPleaseEnter: Please enter the following information:

# templates/review.hamlet

ReviewNothingToReview: Nothing to review!
ReviewAllProblems: All Problems
ReviewNeedingReview: Needing Review

# templates/carnap-book.hamlet

CarnapBookTableOfContents: Table of Contents:
CarnapBookChapters: Chapters:
CarnapBookChapter: Chapter
CarnapBookAppendix: Appendix
CarnapBookSpecialSections: Special Sections:
CarnapBookIndexOfRules: Index of Rules
CarnapBookLicense: is licensed under a
