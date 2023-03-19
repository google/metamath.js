include "cphl.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "cocv.mm"
include "cfv.mm"
include "clsm.mm"
include "co.mm"
include "cpj1.mm"
include "wf.mm"
include "cplusg.mm"
include "c0g.mm"
include "ccntz.mm"
include "eqid.mm"
include "clss.mm"
include "csubg.mm"
include "clmod.mm"
include "wss.mm"
include "phllmod.mm"
include "adantr.mm"
include "lsssssubg.mm"
include "syl.mm"
include "wceq.mm"
include "pjdm2.mm"
include "simprbda.mm"
include "sseldd.mm"
include "lssss.mm"
include "ocvlss.mm"
include "syldan.mm"
include "cin.mm"
include "csn.mm"
include "ocvin.mm"
include "cabl.mm"
include "lmodabl.mm"
include "ablcntzd.mm"
include "pj1f.mm"
include "pjval.mm"
include "adantl.mm"
include "eqcomd.mm"
include "simplbda.mm"
include "feq12d.mm"
include "mpbid.mm"

theorem pjf2
  let cT: class T
  let cK: class K
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume pjf.k: |- K = ( proj ` W )
  assume pjf.v: |- V = ( Base ` W )


  assert |- ( ( W e. PreHil /\ T e. dom K ) -> ( K ` T ) : V --> T )

  proof
    cW
    cphl
    wcel
    #
    cT
    cK
    cdm
    wcel
    #
    wa
    #
    cT
    cT
    cW
    cocv
    cfv
    #
    cfv
    #
    cW
    clsm
    cfv
    #
    co
    #
    cT
    cT
    @4
    cW
    cpj1
    cfv
    #
    co
    #
    wf
    cV
    cT
    cT
    cK
    cfv
    #
    wf
    @2
    @7
    cW
    cplusg
    cfv
    #
    @5
    cT
    @4
    cW
    cW
    c0g
    cfv
    #
    cW
    ccntz
    cfv
    #
    @10
    eqid
    @5
    eqid
    #
    @11
    eqid
    #
    @12
    eqid
    #
    @2
    cW
    clss
    cfv
    #
    cW
    csubg
    cfv
    #
    cT
    @2
    cW
    clmod
    wcel
    #
    @16
    @17
    wss
    @0
    @18
    @1
    cW
    phllmod
    adantr
    #
    @16
    cW
    @16
    eqid
    #
    lsssssubg
    syl
    #
    @0
    @1
    cT
    @16
    wcel
    #
    @6
    cV
    wceq
    #
    @5
    cT
    cK
    @16
    @3
    cV
    cW
    pjf.v
    @20
    @3
    eqid
    #
    @13
    pjf.k
    pjdm2
    #
    simprbda
    #
    sseldd
    #
    @2
    @16
    @17
    @4
    @21
    @0
    @1
    cT
    cV
    wss
    #
    @4
    @16
    wcel
    @2
    @22
    @28
    @26
    @16
    cT
    cV
    cW
    pjf.v
    @20
    lssss
    syl
    cT
    @16
    @3
    cV
    cW
    pjf.v
    @24
    @20
    ocvlss
    syldan
    sseldd
    #
    @0
    @1
    @22
    cT
    @4
    cin
    @11
    csn
    wceq
    @26
    cT
    @16
    @3
    cW
    @11
    @24
    @20
    @14
    ocvin
    syldan
    @2
    cT
    @4
    cW
    @12
    @15
    @2
    @18
    cW
    cabl
    wcel
    @19
    cW
    lmodabl
    syl
    @27
    @29
    ablcntzd
    @7
    eqid
    #
    pj1f
    @2
    @6
    cV
    cT
    @8
    @9
    @2
    @9
    @8
    @1
    @9
    @8
    wceq
    @0
    @7
    cT
    cK
    @3
    cW
    @24
    @30
    pjf.k
    pjval
    adantl
    eqcomd
    @0
    @1
    @22
    @23
    @25
    simplbda
    feq12d
    mpbid
end
