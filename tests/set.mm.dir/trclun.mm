include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "cab.mm"
include "cint.mm"
include "ctcl.mm"
include "cfv.mm"
include "unss.mm"
include "simpl.mm"
include "sylbir.mm"
include "vex.mm"
include "trcleq2lem.mm"
include "elab.mm"
include "biimpri.mm"
include "sylan.mm"
include "intss1.mm"
include "syl.mm"
include "simpr.mm"
include "unssd.mm"
include "jca.mm"
include "ssmin.mm"
include "unss12.mm"
include "mp2an.mm"
include "sstr.mm"
include "mpan.mm"
include "anim1i.mm"
include "impbii.mm"
include "abbii.mm"
include "inteqi.mm"
include "cvv.mm"
include "wceq.mm"
include "unexg.mm"
include "trclfv.mm"
include "uneq12d.mm"
include "fveq2d.mm"
include "fvex.mm"
include "syl6eqelr.mm"
include "syl2an.mm"
include "eqtrd.mm"
include "3eqtr4a.mm"

theorem trclun
  let cR: class R
  let cS: class S
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vx: setvar x
  let vs: setvar s


  assert |- ( ( R e. V /\ S e. W ) -> ( t+ ` ( R u. S ) ) = ( t+ ` ( ( t+ ` R ) u. ( t+ ` S ) ) ) )

  proof
    cR
    cV
    wcel
    #
    cS
    cW
    wcel
    #
    wa
    #
    cR
    cS
    cun
    #
    vx
    cv
    #
    wss
    #
    @4
    @4
    ccom
    @4
    wss
    #
    wa
    #
    vx
    cab
    #
    cint
    #
    cR
    vr
    cv
    #
    wss
    @10
    @10
    ccom
    @10
    wss
    #
    wa
    #
    vr
    cab
    #
    cint
    #
    cS
    vs
    cv
    #
    wss
    @15
    @15
    ccom
    @15
    wss
    #
    wa
    #
    vs
    cab
    #
    cint
    #
    cun
    #
    @4
    wss
    #
    @6
    wa
    #
    vx
    cab
    #
    cint
    #
    @3
    ctcl
    cfv
    #
    cR
    ctcl
    cfv
    #
    cS
    ctcl
    cfv
    #
    cun
    #
    ctcl
    cfv
    #
    @8
    @23
    @7
    @22
    vx
    @7
    @22
    @7
    @21
    @6
    @7
    @14
    @19
    @4
    @7
    @4
    @13
    wcel
    #
    @14
    @4
    wss
    @5
    cR
    @4
    wss
    #
    @6
    @30
    @5
    @31
    cS
    @4
    wss
    #
    wa
    #
    @31
    cR
    cS
    @4
    unss
    #
    @31
    @32
    simpl
    sylbir
    @30
    @31
    @6
    wa
    #
    @12
    @35
    vr
    @4
    vx
    vex
    #
    @10
    @4
    cR
    trcleq2lem
    elab
    biimpri
    sylan
    @4
    @13
    intss1
    syl
    @7
    @4
    @18
    wcel
    #
    @19
    @4
    wss
    @5
    @32
    @6
    @37
    @5
    @33
    @32
    @34
    @31
    @32
    simpr
    sylbir
    @37
    @32
    @6
    wa
    #
    @17
    @38
    vs
    @4
    @36
    @15
    @4
    cS
    trcleq2lem
    elab
    biimpri
    sylan
    @4
    @18
    intss1
    syl
    unssd
    @5
    @6
    simpr
    jca
    @21
    @5
    @6
    @3
    @20
    wss
    #
    @21
    @5
    cR
    @14
    wss
    cS
    @19
    wss
    @39
    @11
    vr
    cR
    ssmin
    @16
    vs
    cS
    ssmin
    cR
    @14
    cS
    @19
    unss12
    mp2an
    @3
    @20
    @4
    sstr
    mpan
    anim1i
    impbii
    abbii
    inteqi
    @2
    @3
    cvv
    wcel
    @25
    @9
    wceq
    cR
    cS
    cV
    cW
    unexg
    vx
    @3
    cvv
    trclfv
    syl
    @2
    @29
    @20
    ctcl
    cfv
    #
    @24
    @2
    @28
    @20
    ctcl
    @2
    @26
    @14
    @27
    @19
    @2
    @0
    @26
    @14
    wceq
    @0
    @1
    simpl
    vr
    cR
    cV
    trclfv
    #
    syl
    @2
    @1
    @27
    @19
    wceq
    @0
    @1
    simpr
    vs
    cS
    cW
    trclfv
    #
    syl
    uneq12d
    fveq2d
    @2
    @20
    cvv
    wcel
    #
    @40
    @24
    wceq
    @0
    @14
    cvv
    wcel
    @19
    cvv
    wcel
    @43
    @1
    @0
    @14
    @26
    cvv
    @41
    cR
    ctcl
    fvex
    syl6eqelr
    @1
    @19
    @27
    cvv
    @42
    cS
    ctcl
    fvex
    syl6eqelr
    @14
    @19
    cvv
    cvv
    unexg
    syl2an
    vx
    @20
    cvv
    trclfv
    syl
    eqtrd
    3eqtr4a
end
