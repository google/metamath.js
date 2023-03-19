include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "cplusg.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "c1.mm"
include "cseq.mm"
include "co.mm"
include "wceq.mm"
include "nncn.mm"
include "negnegd.mm"
include "adantr.mm"
include "fveq2d.mm"
include "cc0.mm"
include "c0g.mm"
include "clt.mm"
include "wbr.mm"
include "cif.mm"
include "cz.mm"
include "nnnegz.mm"
include "eqid.mm"
include "mulgval.mm"
include "sylan.mm"
include "wne.mm"
include "wn.mm"
include "nnne0.mm"
include "cc.mm"
include "wb.mm"
include "negeq0.mm"
include "necon3abid.mm"
include "syl.mm"
include "mpbid.mm"
include "iffalsed.mm"
include "cr.mm"
include "nnre.mm"
include "renegcld.mm"
include "nngt0.mm"
include "lt0neg2d.mm"
include "wi.mm"
include "0re.mm"
include "ltnsym.mm"
include "mpan2.mm"
include "sylc.mm"
include "eqtrd.mm"
include "mulgnn.mm"
include "3eqtr4d.mm"

theorem mulgnegnn
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cI: class I
  let cN: class N
  let cX: class X
  assume mulg1.b: |- B = ( Base ` G )
  assume mulg1.m: |- .x. = ( .g ` G )
  assume mulgnegnn.i: |- I = ( invg ` G )


  assert |- ( ( N e. NN /\ X e. B ) -> ( -u N .x. X ) = ( I ` ( N .x. X ) ) )

  proof
    cN
    cn
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cN
    cneg
    #
    cneg
    #
    cG
    cplusg
    cfv
    #
    cn
    cX
    csn
    cxp
    c1
    cseq
    #
    cfv
    #
    cI
    cfv
    #
    cN
    @6
    cfv
    #
    cI
    cfv
    @3
    cX
    c.x
    co
    #
    cN
    cX
    c.x
    co
    #
    cI
    cfv
    @2
    @7
    @9
    cI
    @2
    @4
    cN
    @6
    @0
    @4
    cN
    wceq
    @1
    @0
    cN
    cN
    nncn
    #
    negnegd
    adantr
    fveq2d
    fveq2d
    @2
    @10
    @3
    cc0
    wceq
    #
    cG
    c0g
    cfv
    #
    cc0
    @3
    clt
    wbr
    #
    @3
    @6
    cfv
    #
    @8
    cif
    #
    cif
    #
    @8
    @0
    @3
    cz
    wcel
    @1
    @10
    @18
    wceq
    cN
    nnnegz
    cB
    @5
    @6
    c.x
    cG
    cI
    @3
    cX
    @14
    mulg1.b
    @5
    eqid
    #
    @14
    eqid
    mulgnegnn.i
    mulg1.m
    @6
    eqid
    #
    mulgval
    sylan
    @0
    @18
    @8
    wceq
    @1
    @0
    @18
    @17
    @8
    @0
    @13
    @14
    @17
    @0
    cN
    cc0
    wne
    #
    @13
    wn
    #
    cN
    nnne0
    @0
    cN
    cc
    wcel
    #
    @21
    @22
    wb
    @12
    @23
    @13
    cN
    cc0
    cN
    negeq0
    necon3abid
    syl
    mpbid
    iffalsed
    @0
    @15
    @16
    @8
    @0
    @3
    cr
    wcel
    #
    @3
    cc0
    clt
    wbr
    #
    @15
    wn
    #
    @0
    cN
    cN
    nnre
    #
    renegcld
    @0
    cc0
    cN
    clt
    wbr
    @25
    cN
    nngt0
    @0
    cN
    @27
    lt0neg2d
    mpbid
    @24
    cc0
    cr
    wcel
    @25
    @26
    wi
    0re
    @3
    cc0
    ltnsym
    mpan2
    sylc
    iffalsed
    eqtrd
    adantr
    eqtrd
    @2
    @11
    @9
    cI
    cB
    @5
    @6
    c.x
    cG
    cN
    cX
    mulg1.b
    @19
    mulg1.m
    @20
    mulgnn
    fveq2d
    3eqtr4d
end
