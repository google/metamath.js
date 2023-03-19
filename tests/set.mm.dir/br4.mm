include "cop.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wcel.mm"
include "wa.mm"
include "opex.mm"
include "eqeq1.mm"
include "3anbi1d.mm"
include "rexbidv.mm"
include "2rexbidv.mm"
include "3anbi2d.mm"
include "brab.mm"
include "wi.mm"
include "wb.mm"
include "vex.mm"
include "opth.mm"
include "sylan9bb.mm"
include "sylbi.mm"
include "eqcoms.mm"
include "biimp3a.mm"
include "a1i.mm"
include "rexlimdva.mm"
include "rexlimdvva.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "eqidd.mm"
include "simpr.mm"
include "opeq1.mm"
include "eqeq2d.mm"
include "3anbi23d.mm"
include "opeq2.mm"
include "rspc2ev.mm"
include "syl113anc.mm"
include "3anbi13d.mm"
include "syl3anc.mm"
include "rexeqdv.mm"
include "rexeqbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "impbid.mm"
include "syl5bb.mm"

theorem br4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cX: class X
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume br4.1: |- ( a = A -> ( ph <-> ps ) )
  assume br4.2: |- ( b = B -> ( ps <-> ch ) )
  assume br4.3: |- ( c = C -> ( ch <-> th ) )
  assume br4.4: |- ( d = D -> ( th <-> ta ) )
  assume br4.5: |- ( x = X -> P = Q )
  assume br4.6: |- R = { <. p , q >. | E. x e. S E. a e. P E. b e. P E. c e. P E. d e. P ( p = <. a , b >. /\ q = <. c , d >. /\ ph ) }

  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a p
  disjoint a q
  disjoint a x
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint b p
  disjoint b q
  disjoint b x
  disjoint A b
  disjoint c d
  disjoint c p
  disjoint c q
  disjoint c x
  disjoint A c
  disjoint d p
  disjoint d q
  disjoint d x
  disjoint A d
  disjoint p q
  disjoint p x
  disjoint A p
  disjoint q x
  disjoint A q
  disjoint A x
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B p
  disjoint B q
  disjoint B x
  disjoint b ch
  disjoint Q a
  disjoint Q b
  disjoint Q c
  disjoint Q d
  disjoint Q x
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C p
  disjoint C q
  disjoint C x
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D p
  disjoint D q
  disjoint D x
  disjoint a ps
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X x
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint P p
  disjoint P q
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S p
  disjoint S q
  disjoint S x
  disjoint a ta
  disjoint b ta
  disjoint c ta
  disjoint d ta
  disjoint ta x
  disjoint c th
  disjoint p ph
  disjoint ph q
  disjoint ph x
  assert |- ( ( X e. S /\ ( A e. Q /\ B e. Q ) /\ ( C e. Q /\ D e. Q ) ) -> ( <. A , B >. R <. C , D >. <-> ta ) )

  proof
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    cR
    wbr
    @0
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    wceq
    #
    @1
    vc
    cv
    #
    vd
    cv
    #
    cop
    #
    wceq
    #
    wph
    w3a
    #
    vd
    cP
    wrex
    #
    vc
    cP
    wrex
    #
    vb
    cP
    wrex
    #
    va
    cP
    wrex
    #
    vx
    cS
    wrex
    #
    cX
    cS
    wcel
    #
    cA
    cQ
    wcel
    #
    cB
    cQ
    wcel
    #
    wa
    #
    cC
    cQ
    wcel
    #
    cD
    cQ
    wcel
    #
    wa
    #
    w3a
    #
    wta
    vp
    cv
    #
    @4
    wceq
    #
    vq
    cv
    #
    @8
    wceq
    #
    wph
    w3a
    #
    vd
    cP
    wrex
    #
    vc
    cP
    wrex
    vb
    cP
    wrex
    #
    va
    cP
    wrex
    vx
    cS
    wrex
    @5
    @27
    wph
    w3a
    #
    vd
    cP
    wrex
    #
    vc
    cP
    wrex
    vb
    cP
    wrex
    #
    va
    cP
    wrex
    vx
    cS
    wrex
    @15
    vp
    vq
    @0
    @1
    cR
    cA
    cB
    opex
    cC
    cD
    opex
    @24
    @0
    wceq
    #
    @30
    @33
    vx
    va
    cS
    cP
    @34
    @29
    @32
    vb
    vc
    cP
    cP
    @34
    @28
    @31
    vd
    cP
    @34
    @25
    @5
    @27
    wph
    @24
    @0
    @4
    eqeq1
    3anbi1d
    rexbidv
    2rexbidv
    2rexbidv
    @26
    @1
    wceq
    #
    @33
    @13
    vx
    va
    cS
    cP
    @35
    @32
    @11
    vb
    vc
    cP
    cP
    @35
    @31
    @10
    vd
    cP
    @35
    @27
    @9
    @5
    wph
    @26
    @1
    @8
    eqeq1
    3anbi2d
    rexbidv
    2rexbidv
    2rexbidv
    br4.6
    brab
    @23
    @15
    wta
    @23
    @13
    wta
    vx
    va
    cS
    cP
    @23
    vx
    cv
    #
    cS
    wcel
    @2
    cP
    wcel
    wa
    wa
    #
    @11
    wta
    vb
    vc
    cP
    cP
    @37
    @3
    cP
    wcel
    @6
    cP
    wcel
    wa
    wa
    #
    @10
    wta
    vd
    cP
    @10
    wta
    wi
    @38
    @7
    cP
    wcel
    wa
    @5
    @9
    wph
    wta
    @5
    wph
    wch
    @9
    wta
    wph
    wch
    wb
    #
    @4
    @0
    @4
    @0
    wceq
    @2
    cA
    wceq
    #
    @3
    cB
    wceq
    #
    wa
    @39
    @2
    @3
    cA
    cB
    va
    vex
    vb
    vex
    opth
    @40
    wph
    wps
    @41
    wch
    br4.1
    br4.2
    sylan9bb
    sylbi
    eqcoms
    wch
    wta
    wb
    #
    @8
    @1
    @8
    @1
    wceq
    @6
    cC
    wceq
    #
    @7
    cD
    wceq
    #
    wa
    @42
    @6
    @7
    cC
    cD
    vc
    vex
    vd
    vex
    opth
    @43
    wch
    wth
    @44
    wta
    br4.3
    br4.4
    sylan9bb
    sylbi
    eqcoms
    sylan9bb
    biimp3a
    a1i
    rexlimdva
    rexlimdvva
    rexlimdvva
    @23
    wta
    @15
    @23
    wta
    wa
    #
    @16
    @10
    vd
    cQ
    wrex
    #
    vc
    cQ
    wrex
    #
    vb
    cQ
    wrex
    #
    va
    cQ
    wrex
    #
    @15
    @16
    @19
    @22
    wta
    simpl1
    @45
    @17
    @18
    @0
    @0
    wceq
    #
    @9
    wch
    w3a
    #
    vd
    cQ
    wrex
    vc
    cQ
    wrex
    #
    @49
    @17
    @18
    @16
    @22
    wta
    simpl2l
    @17
    @18
    @16
    @22
    wta
    simpl2r
    @45
    @20
    @21
    @50
    @1
    @1
    wceq
    #
    wta
    @52
    @20
    @21
    @16
    @19
    wta
    simpl3l
    @20
    @21
    @16
    @19
    wta
    simpl3r
    @45
    @0
    eqidd
    @45
    @1
    eqidd
    @23
    wta
    simpr
    @51
    @50
    @53
    wta
    w3a
    @50
    @1
    cC
    @7
    cop
    #
    wceq
    #
    wth
    w3a
    vc
    vd
    cC
    cD
    cQ
    cQ
    @43
    @9
    @55
    wch
    wth
    @50
    @43
    @8
    @54
    @1
    @6
    cC
    @7
    opeq1
    eqeq2d
    br4.3
    3anbi23d
    @44
    @55
    @53
    wth
    wta
    @50
    @44
    @54
    @1
    @1
    @7
    cD
    cC
    opeq2
    eqeq2d
    br4.4
    3anbi23d
    rspc2ev
    syl113anc
    @47
    @52
    @0
    cA
    @3
    cop
    #
    wceq
    #
    @9
    wps
    w3a
    #
    vd
    cQ
    wrex
    vc
    cQ
    wrex
    va
    vb
    cA
    cB
    cQ
    cQ
    @40
    @10
    @58
    vc
    vd
    cQ
    cQ
    @40
    @5
    @57
    wph
    wps
    @9
    @40
    @4
    @56
    @0
    @2
    cA
    @3
    opeq1
    eqeq2d
    br4.1
    3anbi13d
    2rexbidv
    @41
    @58
    @51
    vc
    vd
    cQ
    cQ
    @41
    @57
    @50
    wps
    wch
    @9
    @41
    @56
    @0
    @0
    @3
    cB
    cA
    opeq2
    eqeq2d
    br4.2
    3anbi13d
    2rexbidv
    rspc2ev
    syl3anc
    @14
    @49
    vx
    cX
    cS
    @36
    cX
    wceq
    #
    @13
    @48
    va
    cP
    cQ
    br4.5
    @59
    @12
    @47
    vb
    cP
    cQ
    br4.5
    @59
    @11
    @46
    vc
    cP
    cQ
    br4.5
    @59
    @10
    vd
    cP
    cQ
    br4.5
    rexeqdv
    rexeqbidv
    rexeqbidv
    rexeqbidv
    rspcev
    syl2anc
    ex
    impbid
    syl5bb
end
