# templates/homepage.hamlet
HomepageWelcome: Carnap.io sitesine hoş geldiniz!
HomepageSubtitle: Haskell için formel mantık çerçevesi
HomepageHeader: Arkaplan
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
InfopageAboutCarnap: Carnap Hakkında
InfopageWhatIs: Carnap Nedir?
InfopageWhatFor: Carnap Ne İşe Yarar?
InfopageHowToUse: Carnap'ı Nasıl Kullanabilirim?
InfopageWhyName: Neden “Carnap”?
InfopageWhoUses: Carnap'ı Kim Kullanır?
InfopageHowWorks: Carnap Nasıl Çalışır?
InfopageHowHelp: Nasıl Dahil Olabilirim?
InfopageCarnapQuote1: “Soyut dilsel biçimlerin kabulü ya da reddi, tıpkı herhangi bir bilim dalındaki diğer herhangi bir dil biçiminin kabulü ya da reddi gibi, nihai olarak, elde edilen sonucun gereken çabanın miktarı ve karmaşıklığına oranı yani araç olarak verimlilik tarafından kararlaştırılır. Pratik kullanımdaki başarılarını veya başarısızlıklarını test etmek yerine, belirli dil biçimlerine dogmatik yasaklar koymak, yararsızdan daha kötüdür; kesinlikle zararlıdır çünkü bilimsel ilerlemeyi engelleyebilir.
InfopageCarnapQuote2: ...
Herhangi bir araştırma alanında çalışanlara yararlı buldukları herhangi bir ifade biçimini kullanma özgürlüğü tanıyacağız; sahada çalışmak hiçbir yararlı işlevi olmayan biçimlerin er ya da geç ortadan kaldırılmasına yol açar. Dikkatli olmak istiyoruz: iddialarda bulunurken ve onları incelerken eleştirel ama dilsel biçimleri kabul ederken hoşgörülü olmak istiyoruz.”
InfopageWhatIsText: Carnap is a free and open-source Haskell framework for creating and exploring formal languages, logics, and semantics. It lets you quickly and straightforwardly define languages, construct logics for those languages, and stipulate their semantics. Carnap then uses your specifications to figure out how to check proofs in a variety of formal systems using your logic, how to find the meanings of compound expressions, and a whole lot more.
InfopageDemos: Tanıtım
InfopageDemosHere: Carnap ile yapabileceklerinize birkaç küçük örnek:
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
LayoutAbout: Hakkında
LayoutBook: Kitap
LayoutMessage: İleti
LayoutUserHome: Kullanıcı Ana Sayfa
LayoutInstructorHome: Öğretici Ana Sayfa
LayoutSharedDocuments: Paylaşılmış Belgeler
LayoutSharedDocumentation: Belgeleme
LayoutLogout: Çıkış
LayoutLogin: Giriş

# templates/documentIndex.hamlet

DocumentIndexFilterByTag: Etikete Göre Süz
DocumentIndexPubliclyShared: Herkesle Paylaşılmış
DocumentIndexInstructorsOnly: Yalnızca Öğreticiler

# templates/passwordEntry.hamlet

PasswordEntryRequest: Bu ödev için lütfen erişim anahtarını giriniz

# templates/register.hamlet

RegisterNeedTo: Görünüşe Göre Kayıt Olmanız Gerekiyor
RegisterPleaseEnter: Lütfen aşağıdaki bilgileri giriniz:

# templates/review.hamlet

ReviewNothingToReview: İncelenecek hiçbir şey yok!
ReviewAllProblems: Tüm Problemler
ReviewNeedingReview: İnceleme Gerekiyor

# templates/carnap-book.hamlet

CarnapBookTableOfContents: İçindekiler::
CarnapBookChapters: Bölümler:
CarnapBookChapter: Bölüm
CarnapBookAppendix: Ek
CarnapBookSpecialSections: Özel Kesimler:
CarnapBookIndexOfRules: Kurallar Dizini
CarnapBookLicense: is licensed under a
