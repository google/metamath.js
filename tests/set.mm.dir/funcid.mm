include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cop.mm"
include "cco.mm"
include "chom.mm"
include "wa.mm"
include "cbs.mm"
include "wf.mm"
include "cxp.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmap.mm"
include "cixp.mm"
include "cfunc.mm"
include "wbr.mm"
include "w3a.mm"
include "eqid.mm"
include "ccat.mm"
include "df-br.mm"
include "sylib.mm"
include "funcrcl.mm"
include "syl.mm"
include "simpld.mm"
include "simprd.mm"
include "isfunc.mm"
include "mpbid.mm"
include "simp3d.mm"
include "simpl.mm"
include "ralimi.mm"
include "id.mm"
include "oveq12d.mm"
include "fveq2.mm"
include "fveq12d.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "sylc.mm"

theorem funcid
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.1: class .1.
  let cE: class E
  let cF: class F
  let cG: class G
  let cI: class I
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume funcid.b: |- B = ( Base ` D )
  assume funcid.1: |- .1. = ( Id ` D )
  assume funcid.i: |- I = ( Id ` E )
  assume funcid.f: |- ( ph -> F ( D Func E ) G )
  assume funcid.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( ( X G X ) ` ( .1. ` X ) ) = ( I ` ( F ` X ) ) )

  proof
    wph
    cX
    cB
    wcel
    vx
    cv
    #
    c.1
    cfv
    #
    @0
    @0
    cG
    co
    #
    cfv
    #
    @0
    cF
    cfv
    #
    cI
    cfv
    #
    wceq
    #
    vx
    cB
    wral
    #
    cX
    c.1
    cfv
    #
    cX
    cX
    cG
    co
    #
    cfv
    #
    cX
    cF
    cfv
    #
    cI
    cfv
    #
    wceq
    #
    funcid.x
    wph
    @6
    vn
    cv
    #
    vm
    cv
    #
    @0
    vy
    cv
    #
    cop
    vz
    cv
    #
    cD
    cco
    cfv
    #
    co
    co
    @0
    @17
    cG
    co
    cfv
    @14
    @16
    @17
    cG
    co
    cfv
    @15
    @0
    @16
    cG
    co
    cfv
    @4
    @16
    cF
    cfv
    cop
    @17
    cF
    cfv
    cE
    cco
    cfv
    #
    co
    co
    wceq
    vn
    @16
    @17
    cD
    chom
    cfv
    #
    co
    wral
    vm
    @0
    @16
    @20
    co
    wral
    vz
    cB
    wral
    vy
    cB
    wral
    #
    wa
    #
    vx
    cB
    wral
    #
    @7
    wph
    cB
    cE
    cbs
    cfv
    #
    cF
    wf
    #
    cG
    vz
    cB
    cB
    cxp
    @17
    c1st
    cfv
    cF
    cfv
    @17
    c2nd
    cfv
    cF
    cfv
    cE
    chom
    cfv
    #
    co
    @17
    @20
    cfv
    cmap
    co
    cixp
    wcel
    #
    @23
    wph
    cF
    cG
    cD
    cE
    cfunc
    co
    #
    wbr
    #
    @25
    @27
    @23
    w3a
    funcid.f
    wph
    vx
    vy
    vz
    cB
    @24
    cD
    @18
    c.1
    vm
    vn
    cE
    cF
    cG
    @20
    cI
    @26
    @19
    funcid.b
    @24
    eqid
    @20
    eqid
    @26
    eqid
    funcid.1
    funcid.i
    @18
    eqid
    @19
    eqid
    wph
    cD
    ccat
    wcel
    #
    cE
    ccat
    wcel
    #
    wph
    cF
    cG
    cop
    #
    @28
    wcel
    #
    @30
    @31
    wa
    wph
    @29
    @33
    funcid.f
    cF
    cG
    @28
    df-br
    sylib
    cD
    cE
    @32
    funcrcl
    syl
    #
    simpld
    wph
    @30
    @31
    @34
    simprd
    isfunc
    mpbid
    simp3d
    @22
    @6
    vx
    cB
    @6
    @21
    simpl
    ralimi
    syl
    @6
    @13
    vx
    cX
    cB
    @0
    cX
    wceq
    #
    @3
    @10
    @5
    @12
    @35
    @1
    @8
    @2
    @9
    @35
    @0
    cX
    @0
    cX
    cG
    @35
    id
    #
    @36
    oveq12d
    @0
    cX
    c.1
    fveq2
    fveq12d
    @35
    @4
    @11
    cI
    @0
    cX
    cF
    fveq2
    fveq2d
    eqeq12d
    rspcv
    sylc
end
