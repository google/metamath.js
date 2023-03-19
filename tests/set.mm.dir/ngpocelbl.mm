include "cnlm.mm"
include "wcel.mm"
include "cxr.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cbl.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cxmt.mm"
include "wb.mm"
include "cngp.mm"
include "cme.mm"
include "nlmngp.mm"
include "ngpmet.mm"
include "metxmet.mm"
include "3syl.mm"
include "anim1i.mm"
include "3adant3.mm"
include "simp3l.mm"
include "cgrp.mm"
include "ngpgrp.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "3anass.mm"
include "sylanbrc.mm"
include "grpcl.mm"
include "jca.mm"
include "elbl2.mm"
include "cds.mm"
include "csg.mm"
include "wceq.mm"
include "cxp.mm"
include "cres.mm"
include "oveqi.mm"
include "ovres.mm"
include "syl5eq.mm"
include "eqid.mm"
include "ngpdsr.mm"
include "syl3anc.mm"
include "cabl.mm"
include "clmod.mm"
include "nlmlmod.mm"
include "lmodabl.mm"
include "ablpncan2.mm"
include "fveq2d.mm"
include "3eqtrd.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem ngpocelbl
  let cA: class A
  let cD: class D
  let cP: class P
  let c.pl: class .+
  let cR: class R
  let cG: class G
  let cN: class N
  let cX: class X
  assume ngpocelbl.n: |- N = ( norm ` G )
  assume ngpocelbl.x: |- X = ( Base ` G )
  assume ngpocelbl.p: |- .+ = ( +g ` G )
  assume ngpocelbl.d: |- D = ( ( dist ` G ) |` ( X X. X ) )


  assert |- ( ( G e. NrmMod /\ R e. RR* /\ ( P e. X /\ A e. X ) ) -> ( ( P .+ A ) e. ( P ( ball ` D ) R ) <-> ( N ` A ) < R ) )

  proof
    cG
    cnlm
    wcel
    #
    cR
    cxr
    wcel
    #
    cP
    cX
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    w3a
    #
    cP
    cA
    c.pl
    co
    #
    cP
    cR
    cD
    cbl
    cfv
    co
    wcel
    #
    cP
    @6
    cD
    co
    #
    cR
    clt
    wbr
    #
    cA
    cN
    cfv
    #
    cR
    clt
    wbr
    @5
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @1
    wa
    #
    @2
    @6
    cX
    wcel
    #
    wa
    #
    wa
    @7
    @9
    wb
    @5
    @12
    @14
    @0
    @1
    @12
    @4
    @0
    @11
    @1
    @0
    cG
    cngp
    wcel
    #
    cD
    cX
    cme
    cfv
    wcel
    @11
    cG
    nlmngp
    #
    cD
    cG
    cX
    ngpocelbl.x
    ngpocelbl.d
    ngpmet
    cD
    cX
    metxmet
    3syl
    anim1i
    3adant3
    @5
    @2
    @13
    @0
    @1
    @2
    @3
    simp3l
    #
    @5
    cG
    cgrp
    wcel
    #
    @2
    @3
    w3a
    #
    @13
    @5
    @18
    @4
    @19
    @0
    @1
    @18
    @4
    @0
    @15
    @18
    @16
    cG
    ngpgrp
    syl
    3ad2ant1
    @0
    @1
    @4
    simp3
    #
    @18
    @2
    @3
    3anass
    sylanbrc
    cX
    c.pl
    cG
    cP
    cA
    ngpocelbl.x
    ngpocelbl.p
    grpcl
    syl
    #
    jca
    #
    jca
    @6
    cD
    cP
    cR
    cX
    elbl2
    syl
    @5
    @8
    @10
    cR
    clt
    @5
    @8
    cP
    @6
    cG
    cds
    cfv
    #
    co
    #
    @6
    cP
    cG
    csg
    cfv
    #
    co
    #
    cN
    cfv
    #
    @10
    @5
    @14
    @8
    @24
    wceq
    @22
    @14
    @8
    cP
    @6
    @23
    cX
    cX
    cxp
    cres
    #
    co
    @24
    cD
    @28
    cP
    @6
    ngpocelbl.d
    oveqi
    cP
    @6
    cX
    cX
    @23
    ovres
    syl5eq
    syl
    @5
    @15
    @2
    @13
    @24
    @27
    wceq
    @0
    @1
    @15
    @4
    @16
    3ad2ant1
    @17
    @21
    cP
    @6
    @23
    cG
    @25
    cN
    cX
    ngpocelbl.n
    ngpocelbl.x
    @25
    eqid
    #
    @23
    eqid
    ngpdsr
    syl3anc
    @5
    @26
    cA
    cN
    @5
    cG
    cabl
    wcel
    #
    @2
    @3
    w3a
    #
    @26
    cA
    wceq
    @5
    @30
    @4
    @31
    @0
    @1
    @30
    @4
    @0
    cG
    clmod
    wcel
    @30
    cG
    nlmlmod
    cG
    lmodabl
    syl
    3ad2ant1
    @20
    @30
    @2
    @3
    3anass
    sylanbrc
    cX
    c.pl
    cG
    @25
    cP
    cA
    ngpocelbl.x
    ngpocelbl.p
    @29
    ablpncan2
    syl
    fveq2d
    3eqtrd
    breq1d
    bitrd
end
