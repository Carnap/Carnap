# templates/homepage.hamlet
HomepageWelcome: Welcome to Carnap.io
HomepageSubtitle: A formal logic framework for Haskell
HomepageHeader: Background
HomepageText1: Carnap is a free and open software framework written in
HomepageText2: for teaching and studying formal logic. Carnap powers logic courses at
HomepageText3: dozens of colleges and universities
HomepageText4: around the world.
HomepageText5: If you're a student in a course that uses Carnap, please follow the links at the top of the page to log in and to access course materials.
HomepageText6: If you're just curious about Carnap, you can find some general information on our
HomepageText7: about
HomepageText8: page. If you're interested in the project, and would like to use Carnap in a class you're teaching, or get involved in some other way, please feel free to 
HomepageText9: get in touch!

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
InfopageWhatIsText: Carnap is a free and open-source Haskell framework for creating and exploring formal languages, logics, and semantics. It lets you quickly and straightforwardly define languages, construct logics for those languages, and stipulate their semantics. Carnap then uses your specifications to figure out how to check proofs in a variety of formal systems using your logic, how to find the meanings of compound expressions, and a whole lot more.
InfopageDemos: Demos
InfopageDemosHere: Here are some quick examples of what Carnap can do.
InfopageDemosText1: This is a proofbox with a Kalish and Montague System for Propositional Logic. You can directly manipulate the proof by typing in the proofbox, and see the effects of your changes by mousing over the line-decorations on the right hand side. 
InfopageDemosText2: This is a rendering proofbox with a Kalish and Montague System for Propositional Logic, which also visually displays the structure of the proof being developed.
InfopageDemosText3: This is a rendering proofbox with Hardegree's variation on a Montague system.
InfopageDemosText4: This is a proofbox with a Fitch system, using rules from 
InfopageDemosText5: and visually rendering the proof structure in the Fitch style.
InfopageDemosText6: This is a proofbox with a Kalish and Montague System for First-Order Logic, displaying a proof of Russell's Theorem.
InfopageDemosText7: This is a proof with Goldfarb's Lemmon-style system of natural deduction, from the textbook 
InfopageDemosText8: Here’s a proof of the fact that the bisectors of the sides of a triangle always meet at a point (from the assumption that a point is on the bisector of a segment if and only if it’s equidistant from the endpoints of that segment). “F(x,y)” abbreviates that “x is on y“, “g(y,z)” abbreviates “the bisector of the segment given by y and z”, and “h(x,z)” abbreviates “the distance from x to z”.
InfopageDemosText9: (Because of the number of variables, this one may take a moment to load initially. Once loaded, it should respond quickly to changes.)
InfopageDemosText10: Here are two more proofs of Russell's theorem, this time using a version of system QL, from P.D. Magnus' free and open textbook 
InfopageDemosText11: , and the system FOL from the 
InfopageDemosText12: of
InfopageDemosText13: Note that we've changed how formulas are parsed (dropping the parentheses around the arguments to predicates), to match the display style of 
InfopageDemosText14: This is a proofbox with a Kalish and Montague System for Monadic Second-Order Logic, showing how to prove an instance of the comprehension scheme, using a predicate abstraction rule.
InfopageDemosText15: This is a proof that every relation has an inverse, in a system of arbitrarily (finitely) Polyadic Second-Order Logic, again making use of a predicate abstraction rule.
InfopageDemosText16: This is a proof that the powerset of a transitive set is transitive (exercise 3, chapter 3.3 from Velleman's #
InfopageDemosText17: ), in a system of elementary set theory.
InfopageDemosText18: Here are proofs of axioms 5 and B within natural deduction systems for propositional modal logics K5 and KTB, in the style of Hardegree's 
InfopageDemosText19: These use 
InfopageDemosText20: for nicer-looking logical symbols and use guards to help visually indicate the scope of each subproof.
InfopageDemosText21: Here's a proof of the Barcan Formula within a naïvely quantified system of modal logic, based on the system MPL of Hardegree's #
InfopageDemosText22: Carnap supports proofs written in the sequent calculus, via 
InfopageDemosText23: Among the systems supported are propositional and first order variants of Gentzen's original LK and LJ.
InfopageDemosText24: Carnap also includes a JSON API, making it possible to create pure JavaScript GUIs that use Carnap under the hood for in-browser proof checking. Here's an example of such a GUI, adapted from 
InfopageDemosText25: using P.D. Magnus' 
InfopageDemosText26: system SL.
InfopageDemosText27: example 17

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
