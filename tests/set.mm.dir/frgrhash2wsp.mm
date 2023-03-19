include "cfrgr.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "c2.mm"
include "cwwspthsn.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "cwwspthsnon.mm"
include "ciun.mm"
include "c1.mm"
include "cmin.mm"
include "cmul.mm"
include "wceq.mm"
include "cn.mm"
include "2nn.mm"
include "wspniunwspnon.mm"
include "mpan.mm"
include "fveq2d.mm"
include "adantr.mm"
include "simpr.mm"
include "eqid.mm"
include "cvtx.mm"
include "eleq1i.mm"
include "wspthnonfi.mm"
include "sylbi.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "wdisj.mm"
include "2wspiundisj.mm"
include "a1i.mm"
include "2wspdisj.mm"
include "wne.mm"
include "simplll.mm"
include "eldifi.mm"
include "anim12i.mm"
include "eldifsni.mm"
include "necomd.mm"
include "frgr2wsp1.mm"
include "syl3anc.mm"
include "3impa.mm"
include "hash2iun1dif1.mm"
include "eqtrd.mm"

theorem frgrhash2wsp
  let cG: class G
  let cV: class V
  let va: setvar a
  let vb: setvar b
  assume frgrhash2wsp.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FriendGraph /\ V e. Fin ) -> ( # ` ( 2 WSPathsN G ) ) = ( ( # ` V ) x. ( ( # ` V ) - 1 ) ) )

  proof
    cG
    cfrgr
    wcel
    #
    cV
    cfn
    wcel
    #
    wa
    #
    c2
    cG
    cwwspthsn
    co
    #
    chash
    cfv
    #
    va
    cV
    vb
    cV
    va
    cv
    #
    csn
    #
    cdif
    #
    @5
    vb
    cv
    #
    c2
    cG
    cwwspthsnon
    co
    co
    #
    ciun
    #
    ciun
    #
    chash
    cfv
    #
    cV
    chash
    cfv
    #
    @13
    c1
    cmin
    co
    cmul
    co
    @0
    @4
    @12
    wceq
    @1
    @0
    @3
    @11
    chash
    c2
    cn
    wcel
    @0
    @3
    @11
    wceq
    2nn
    va
    vb
    cfrgr
    cG
    c2
    cV
    frgrhash2wsp.v
    wspniunwspnon
    mpan
    fveq2d
    adantr
    @2
    va
    vb
    cV
    @7
    @9
    @0
    @1
    simpr
    @7
    eqid
    @2
    @5
    cV
    wcel
    #
    @9
    cfn
    wcel
    #
    @8
    @7
    wcel
    #
    @1
    @15
    @0
    @1
    cG
    cvtx
    cfv
    #
    cfn
    wcel
    @15
    cV
    @17
    cfn
    frgrhash2wsp.v
    eleq1i
    @5
    @8
    cG
    c2
    wspthnonfi
    sylbi
    adantl
    3ad2ant1
    va
    cV
    @10
    wdisj
    @2
    cG
    cV
    va
    vb
    2wspiundisj
    a1i
    vb
    @7
    @9
    wdisj
    @2
    @14
    wa
    #
    @5
    cG
    cV
    vb
    2wspdisj
    a1i
    @2
    @14
    @16
    @9
    chash
    cfv
    c1
    wceq
    #
    @18
    @16
    wa
    @0
    @14
    @8
    cV
    wcel
    #
    wa
    @5
    @8
    wne
    #
    @19
    @0
    @1
    @14
    @16
    simplll
    @18
    @14
    @16
    @20
    @2
    @14
    simpr
    @8
    cV
    @6
    eldifi
    anim12i
    @16
    @21
    @18
    @16
    @8
    @5
    @8
    cV
    @5
    eldifsni
    necomd
    adantl
    @5
    @8
    cG
    cV
    frgrhash2wsp.v
    frgr2wsp1
    syl3anc
    3impa
    hash2iun1dif1
    eqtrd
end
