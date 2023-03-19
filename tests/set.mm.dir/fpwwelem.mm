include "wbr.mm"
include "wss.mm"
include "cxp.mm"
include "wa.mm"
include "wwe.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cvv.mm"
include "wcel.mm"
include "wrel.mm"
include "relopabi.mm"
include "a1i.mm"
include "brrelex12.mm"
include "sylan.mm"
include "adantr.mm"
include "simprll.mm"
include "ssexd.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "simprlr.mm"
include "jca.mm"
include "simpl.mm"
include "sseq1d.mm"
include "simpr.mm"
include "sqxpeqd.mm"
include "sseq12d.mm"
include "anbi12d.mm"
include "weeq2.mm"
include "weeq1.mm"
include "sylan9bb.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "raleqbidv.mm"
include "brabga.mm"
include "pm5.21nd.mm"

theorem fpwwelem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cF: class F
  let cW: class W
  let cX: class X
  let vr: setvar r
  let va: setvar a
  let vs: setvar s
  let vu: setvar u
  let vz: setvar z
  let cY: class Y
  assume fpwwe.1: |- W = { <. x , r >. | ( ( x C_ A /\ r C_ ( x X. x ) ) /\ ( r We x /\ A. y e. x ( F ` ( `' r " { y } ) ) = y ) ) }
  assume fpwwe.2: |- ( ph -> A e. _V )

  disjoint r x
  disjoint A r
  disjoint A x
  disjoint r y
  disjoint F r
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint ph r
  disjoint ph x
  disjoint ph y
  disjoint R r
  disjoint R x
  disjoint R y
  disjoint X r
  disjoint X x
  disjoint X y
  disjoint W r
  disjoint W x
  disjoint W y
  disjoint a r
  disjoint a s
  disjoint a x
  disjoint A a
  disjoint r s
  disjoint s x
  disjoint A s
  disjoint a u
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint r u
  disjoint r z
  disjoint s u
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint ph u
  disjoint R u
  disjoint X u
  disjoint Y r
  disjoint Y u
  disjoint Y x
  disjoint Y y
  disjoint W u
  assert |- ( ph -> ( X W R <-> ( ( X C_ A /\ R C_ ( X X. X ) ) /\ ( R We X /\ A. y e. X ( F ` ( `' R " { y } ) ) = y ) ) ) )

  proof
    wph
    cX
    cR
    cW
    wbr
    #
    cX
    cA
    wss
    #
    cR
    cX
    cX
    cxp
    #
    wss
    #
    wa
    #
    cX
    cR
    wwe
    #
    cR
    ccnv
    #
    vy
    cv
    #
    csn
    #
    cima
    #
    cF
    cfv
    #
    @7
    wceq
    #
    vy
    cX
    wral
    #
    wa
    #
    wa
    #
    cX
    cvv
    wcel
    #
    cR
    cvv
    wcel
    #
    wa
    #
    wph
    cW
    wrel
    #
    @0
    @17
    @18
    wph
    vx
    cv
    #
    cA
    wss
    #
    vr
    cv
    #
    @19
    @19
    cxp
    #
    wss
    #
    wa
    #
    @19
    @21
    wwe
    #
    @21
    ccnv
    #
    @8
    cima
    #
    cF
    cfv
    #
    @7
    wceq
    #
    vy
    @19
    wral
    #
    wa
    #
    wa
    #
    vx
    vr
    cW
    fpwwe.1
    relopabi
    a1i
    cX
    cR
    cW
    brrelex12
    sylan
    wph
    @14
    wa
    #
    @15
    @16
    @33
    cX
    cA
    cvv
    wph
    cA
    cvv
    wcel
    @14
    fpwwe.2
    adantr
    wph
    @1
    @3
    @13
    simprll
    ssexd
    #
    @33
    cR
    @2
    cvv
    @33
    @15
    @15
    @2
    cvv
    wcel
    @34
    @34
    cX
    cX
    cvv
    cvv
    xpexg
    syl2anc
    wph
    @1
    @3
    @13
    simprlr
    ssexd
    jca
    @32
    @14
    vx
    vr
    cX
    cR
    cW
    cvv
    cvv
    @19
    cX
    wceq
    #
    @21
    cR
    wceq
    #
    wa
    #
    @24
    @4
    @31
    @13
    @37
    @20
    @1
    @23
    @3
    @37
    @19
    cX
    cA
    @35
    @36
    simpl
    #
    sseq1d
    @37
    @21
    cR
    @22
    @2
    @35
    @36
    simpr
    #
    @37
    @19
    cX
    @38
    sqxpeqd
    sseq12d
    anbi12d
    @37
    @25
    @5
    @30
    @12
    @35
    @25
    cX
    @21
    wwe
    @36
    @5
    @19
    cX
    @21
    weeq2
    cX
    @21
    cR
    weeq1
    sylan9bb
    @37
    @29
    @11
    vy
    @19
    cX
    @38
    @37
    @28
    @10
    @7
    @37
    @27
    @9
    cF
    @37
    @26
    @6
    @8
    @37
    @21
    cR
    @39
    cnveqd
    imaeq1d
    fveq2d
    eqeq1d
    raleqbidv
    anbi12d
    anbi12d
    fpwwe.1
    brabga
    pm5.21nd
end
