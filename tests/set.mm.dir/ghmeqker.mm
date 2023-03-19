include "cghm.mm"
include "co.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "c0g.mm"
include "wceq.mm"
include "wa.mm"
include "csg.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "sneqi.mm"
include "imaeq2i.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "wfn.mm"
include "wb.mm"
include "cbs.mm"
include "wf.mm"
include "eqid.mm"
include "ghmf.mm"
include "ffn.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "fniniseg.mm"
include "syl5bb.mm"
include "cgrp.mm"
include "ghmgrp1.mm"
include "grpsubcl.mm"
include "syl3an1.mm"
include "biantrurd.mm"
include "ghmsub.mm"
include "eqeq1d.mm"
include "bitr3d.mm"
include "ghmgrp2.mm"
include "simp2.mm"
include "ffvelrnd.mm"
include "simp3.mm"
include "grpsubeq0.mm"
include "syl3anc.mm"
include "3bitrrd.mm"

theorem ghmeqker
  let cB: class B
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cK: class K
  let c.mi: class .-
  let cV: class V
  let c.0: class .0.
  assume ghmeqker.b: |- B = ( Base ` S )
  assume ghmeqker.z: |- .0. = ( 0g ` T )
  assume ghmeqker.k: |- K = ( `' F " { .0. } )
  assume ghmeqker.m: |- .- = ( -g ` S )


  assert |- ( ( F e. ( S GrpHom T ) /\ U e. B /\ V e. B ) -> ( ( F ` U ) = ( F ` V ) <-> ( U .- V ) e. K ) )

  proof
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cU
    cB
    wcel
    #
    cV
    cB
    wcel
    #
    w3a
    #
    cU
    cV
    c.mi
    co
    #
    cK
    wcel
    #
    @4
    cB
    wcel
    #
    @4
    cF
    cfv
    #
    cT
    c0g
    cfv
    #
    wceq
    #
    wa
    #
    cU
    cF
    cfv
    #
    cV
    cF
    cfv
    #
    cT
    csg
    cfv
    #
    co
    #
    @8
    wceq
    #
    @11
    @12
    wceq
    #
    @5
    @4
    cF
    ccnv
    #
    @8
    csn
    #
    cima
    #
    wcel
    #
    @3
    @10
    cK
    @19
    @4
    cK
    @17
    c.0
    csn
    #
    cima
    @19
    ghmeqker.k
    @21
    @18
    @17
    c.0
    @8
    ghmeqker.z
    sneqi
    imaeq2i
    eqtri
    eleq2i
    @3
    cF
    cB
    wfn
    #
    @20
    @10
    wb
    @0
    @1
    @22
    @2
    @0
    cB
    cT
    cbs
    cfv
    #
    cF
    wf
    #
    @22
    cS
    cT
    cF
    cB
    @23
    ghmeqker.b
    @23
    eqid
    #
    ghmf
    #
    cB
    @23
    cF
    ffn
    syl
    3ad2ant1
    cB
    @8
    @4
    cF
    fniniseg
    syl
    syl5bb
    @3
    @9
    @10
    @15
    @3
    @6
    @9
    @0
    cS
    cgrp
    wcel
    @1
    @2
    @6
    cS
    cT
    cF
    ghmgrp1
    cB
    cS
    c.mi
    cU
    cV
    ghmeqker.b
    ghmeqker.m
    grpsubcl
    syl3an1
    biantrurd
    @3
    @7
    @14
    @8
    cB
    cS
    cT
    cU
    cF
    c.mi
    @13
    cV
    ghmeqker.b
    ghmeqker.m
    @13
    eqid
    #
    ghmsub
    eqeq1d
    bitr3d
    @3
    cT
    cgrp
    wcel
    #
    @11
    @23
    wcel
    @12
    @23
    wcel
    @15
    @16
    wb
    @0
    @1
    @28
    @2
    cS
    cT
    cF
    ghmgrp2
    3ad2ant1
    @3
    cB
    @23
    cU
    cF
    @0
    @1
    @24
    @2
    @26
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    ffvelrnd
    @3
    cB
    @23
    cV
    cF
    @29
    @0
    @1
    @2
    simp3
    ffvelrnd
    @23
    cT
    @13
    @11
    @12
    @8
    @25
    @8
    eqid
    @27
    grpsubeq0
    syl3anc
    3bitrrd
end
