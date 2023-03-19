include "co.mm"
include "cvv.mm"
include "cv.mm"
include "cdm.mm"
include "cmpt.mm"
include "ccom.mm"
include "ciso.mm"
include "cfv.mm"
include "cinv.mm"
include "ccat.mm"
include "wcel.mm"
include "wceq.mm"
include "isofval.mm"
include "syl.mm"
include "coeq2i.mm"
include "3eqtr4g.mm"
include "oveqd.mm"
include "cop.mm"
include "cxp.mm"
include "wfn.mm"
include "csect.mm"
include "ccnv.mm"
include "cin.mm"
include "cmpt2.mm"
include "eqid.mm"
include "ovex.mm"
include "inex1.mm"
include "fnmpt2i.mm"
include "invffval.mm"
include "fneq1d.mm"
include "mpbiri.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "fvco2.mm"
include "df-ov.mm"
include "dmeq.mm"
include "dmex.mm"
include "fvmpt.mm"
include "ax-mp.mm"
include "fveq2i.mm"
include "eqtr3i.mm"
include "eqtrd.mm"

theorem isoval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cI: class I
  let cN: class N
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vz: setvar z
  let cS: class S
  assume invfval.b: |- B = ( Base ` C )
  assume invfval.n: |- N = ( Inv ` C )
  assume invfval.c: |- ( ph -> C e. Cat )
  assume invfval.x: |- ( ph -> X e. B )
  assume invfval.y: |- ( ph -> Y e. B )
  assume isoval.n: |- I = ( Iso ` C )


  assert |- ( ph -> ( X I Y ) = dom ( X N Y ) )

  proof
    wph
    cX
    cY
    cI
    co
    cX
    cY
    vz
    cvv
    vz
    cv
    #
    cdm
    #
    cmpt
    #
    cN
    ccom
    #
    co
    #
    cX
    cY
    cN
    co
    #
    cdm
    #
    wph
    cI
    @3
    cX
    cY
    wph
    cC
    ciso
    cfv
    #
    @2
    cC
    cinv
    cfv
    #
    ccom
    #
    cI
    @3
    wph
    cC
    ccat
    wcel
    @7
    @9
    wceq
    invfval.c
    vz
    cC
    isofval
    syl
    isoval.n
    cN
    @8
    @2
    invfval.n
    coeq2i
    3eqtr4g
    oveqd
    wph
    cX
    cY
    cop
    #
    @3
    cfv
    #
    @10
    cN
    cfv
    #
    @2
    cfv
    #
    @4
    @6
    wph
    cN
    cB
    cB
    cxp
    #
    wfn
    #
    @10
    @14
    wcel
    #
    @11
    @13
    wceq
    wph
    @15
    vx
    vy
    cB
    cB
    vx
    cv
    #
    vy
    cv
    #
    cC
    csect
    cfv
    #
    co
    #
    @18
    @17
    @19
    co
    ccnv
    #
    cin
    #
    cmpt2
    #
    @14
    wfn
    vx
    vy
    cB
    cB
    @22
    @23
    @23
    eqid
    @20
    @21
    @17
    @18
    @19
    ovex
    inex1
    fnmpt2i
    wph
    @14
    cN
    @23
    wph
    vx
    vy
    cB
    cC
    @19
    cN
    cX
    cY
    invfval.b
    invfval.n
    invfval.c
    invfval.x
    invfval.y
    @19
    eqid
    invffval
    fneq1d
    mpbiri
    wph
    cX
    cB
    wcel
    cY
    cB
    wcel
    @16
    invfval.x
    invfval.y
    cX
    cY
    cB
    cB
    opelxpi
    syl2anc
    @14
    @2
    cN
    @10
    fvco2
    syl2anc
    cX
    cY
    @3
    df-ov
    @5
    @2
    cfv
    #
    @6
    @13
    @5
    cvv
    wcel
    @24
    @6
    wceq
    cX
    cY
    cN
    ovex
    #
    vz
    @5
    @1
    @6
    cvv
    @2
    @0
    @5
    dmeq
    @2
    eqid
    @5
    @25
    dmex
    fvmpt
    ax-mp
    @5
    @12
    @2
    cX
    cY
    cN
    df-ov
    fveq2i
    eqtr3i
    3eqtr4g
    eqtrd
end
