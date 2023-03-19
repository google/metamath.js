include "crh.mm"
include "co.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cghm.mm"
include "cmhm.mm"
include "cv.mm"
include "cmgp.mm"
include "cfv.mm"
include "cin.mm"
include "dfrhm2.mm"
include "elmpt2cl.mm"
include "wceq.mm"
include "oveq12.mm"
include "fveq2.mm"
include "oveqan12d.mm"
include "ineq12d.mm"
include "ovex.mm"
include "inex1.mm"
include "ovmpt2a.mm"
include "eleq2d.mm"
include "elin.mm"
include "oveq12i.mm"
include "eqcomi.mm"
include "eleq2i.mm"
include "anbi2i.mm"
include "bitri.mm"
include "syl6bb.mm"
include "biadan2.mm"

theorem isrhm
  let cR: class R
  let cS: class S
  let cF: class F
  let cM: class M
  let cN: class N
  let vr: setvar r
  let vs: setvar s
  assume isrhm.m: |- M = ( mulGrp ` R )
  assume isrhm.n: |- N = ( mulGrp ` S )


  assert |- ( F e. ( R RingHom S ) <-> ( ( R e. Ring /\ S e. Ring ) /\ ( F e. ( R GrpHom S ) /\ F e. ( M MndHom N ) ) ) )

  proof
    cF
    cR
    cS
    crh
    co
    #
    wcel
    #
    cR
    crg
    wcel
    cS
    crg
    wcel
    wa
    #
    cF
    cR
    cS
    cghm
    co
    #
    wcel
    #
    cF
    cM
    cN
    cmhm
    co
    #
    wcel
    #
    wa
    #
    vr
    vs
    crg
    crg
    vr
    cv
    #
    vs
    cv
    #
    cghm
    co
    #
    @8
    cmgp
    cfv
    #
    @9
    cmgp
    cfv
    #
    cmhm
    co
    #
    cin
    #
    cR
    cS
    crh
    cF
    vs
    vr
    dfrhm2
    #
    elmpt2cl
    @2
    @1
    cF
    @3
    cR
    cmgp
    cfv
    #
    cS
    cmgp
    cfv
    #
    cmhm
    co
    #
    cin
    #
    wcel
    #
    @7
    @2
    @0
    @19
    cF
    vr
    vs
    cR
    cS
    crg
    crg
    @14
    @19
    crh
    @8
    cR
    wceq
    #
    @9
    cS
    wceq
    #
    wa
    @10
    @3
    @13
    @18
    @8
    cR
    @9
    cS
    cghm
    oveq12
    @21
    @22
    @11
    @16
    @12
    @17
    cmhm
    @8
    cR
    cmgp
    fveq2
    @9
    cS
    cmgp
    fveq2
    oveqan12d
    ineq12d
    @15
    @3
    @18
    cR
    cS
    cghm
    ovex
    inex1
    ovmpt2a
    eleq2d
    @20
    @4
    cF
    @18
    wcel
    #
    wa
    @7
    cF
    @3
    @18
    elin
    @23
    @6
    @4
    @18
    @5
    cF
    @5
    @18
    cM
    @16
    cN
    @17
    cmhm
    isrhm.m
    isrhm.n
    oveq12i
    eqcomi
    eleq2i
    anbi2i
    bitri
    syl6bb
    biadan2
end
