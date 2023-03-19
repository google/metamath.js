include "cmnd.mm"
include "wcel.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "ccmn.mm"
include "csubmnd.mm"
include "cbs.mm"
include "cmre.mm"
include "cacs.mm"
include "eqid.mm"
include "submacs.mm"
include "adantr.mm"
include "acsmred.mm"
include "simpr.mm"
include "cntzssv.mm"
include "syl6ss.mm"
include "cntzsubm.mm"
include "syldan.mm"
include "mrcsscl.mm"
include "syl3anc.mm"
include "wb.mm"
include "mrcssvd.mm"
include "cntzrec.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "mrccl.mm"
include "submcmn2.mm"
include "syl.mm"
include "mpbird.mm"

theorem cntzspan
  let cS: class S
  let cG: class G
  let cH: class H
  let cK: class K
  let cZ: class Z
  assume cntzspan.z: |- Z = ( Cntz ` G )
  assume cntzspan.k: |- K = ( mrCls ` ( SubMnd ` G ) )
  assume cntzspan.h: |- H = ( G |`s ( K ` S ) )


  assert |- ( ( G e. Mnd /\ S C_ ( Z ` S ) ) -> H e. CMnd )

  proof
    cG
    cmnd
    wcel
    #
    cS
    cS
    cZ
    cfv
    #
    wss
    #
    wa
    #
    cH
    ccmn
    wcel
    #
    cS
    cK
    cfv
    #
    @5
    cZ
    cfv
    #
    wss
    #
    @3
    cG
    csubmnd
    cfv
    #
    cG
    cbs
    cfv
    #
    cmre
    cfv
    wcel
    #
    cS
    @6
    wss
    #
    @6
    @8
    wcel
    #
    @7
    @3
    @8
    @9
    @0
    @8
    @9
    cacs
    cfv
    wcel
    @2
    @9
    cG
    @9
    eqid
    #
    submacs
    adantr
    acsmred
    #
    @3
    @5
    @1
    wss
    #
    @11
    @3
    @10
    @2
    @1
    @8
    wcel
    #
    @15
    @14
    @0
    @2
    simpr
    #
    @0
    @2
    cS
    @9
    wss
    #
    @16
    @3
    cS
    @1
    @9
    @17
    @9
    cS
    cG
    cZ
    @13
    cntzspan.z
    cntzssv
    syl6ss
    #
    @9
    cS
    cG
    cZ
    @13
    cntzspan.z
    cntzsubm
    syldan
    @8
    cS
    cK
    @1
    @9
    cntzspan.k
    mrcsscl
    syl3anc
    @3
    @5
    @9
    wss
    #
    @18
    @15
    @11
    wb
    @3
    @8
    cS
    cK
    @9
    @14
    cntzspan.k
    mrcssvd
    #
    @19
    @9
    @5
    cS
    cG
    cZ
    @13
    cntzspan.z
    cntzrec
    syl2anc
    mpbid
    @0
    @2
    @20
    @12
    @21
    @9
    @5
    cG
    cZ
    @13
    cntzspan.z
    cntzsubm
    syldan
    @8
    cS
    cK
    @6
    @9
    cntzspan.k
    mrcsscl
    syl3anc
    @3
    @5
    @8
    wcel
    #
    @4
    @7
    wb
    @3
    @10
    @18
    @22
    @14
    @19
    @8
    cS
    cK
    @9
    cntzspan.k
    mrccl
    syl2anc
    @5
    cG
    cH
    cZ
    cntzspan.h
    cntzspan.z
    submcmn2
    syl
    mpbird
end
