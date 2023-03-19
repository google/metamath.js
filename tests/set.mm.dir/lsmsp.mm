include "clmod.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cun.mm"
include "cfv.mm"
include "wss.mm"
include "cbs.mm"
include "simp1.mm"
include "eqid.mm"
include "lssss.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "unssd.mm"
include "lspssid.mm"
include "syl2anc.mm"
include "unssad.mm"
include "unssbd.mm"
include "csubg.mm"
include "wa.mm"
include "wb.mm"
include "lsssssubg.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "sseldd.mm"
include "simp3.mm"
include "lspcl.mm"
include "lsmlub.mm"
include "syl3anc.mm"
include "mpbi2and.mm"
include "lsmcl.mm"
include "lsmunss.mm"
include "lspssp.mm"
include "eqssd.mm"

theorem lsmsp
  let c.po: class .(+)
  let cS: class S
  let cT: class T
  let cU: class U
  let cN: class N
  let cW: class W
  assume lsmsp.s: |- S = ( LSubSp ` W )
  assume lsmsp.n: |- N = ( LSpan ` W )
  assume lsmsp.p: |- .(+) = ( LSSum ` W )


  assert |- ( ( W e. LMod /\ T e. S /\ U e. S ) -> ( T .(+) U ) = ( N ` ( T u. U ) ) )

  proof
    cW
    clmod
    wcel
    #
    cT
    cS
    wcel
    #
    cU
    cS
    wcel
    #
    w3a
    #
    cT
    cU
    c.po
    co
    #
    cT
    cU
    cun
    #
    cN
    cfv
    #
    @3
    cT
    @6
    wss
    #
    cU
    @6
    wss
    #
    @4
    @6
    wss
    #
    @3
    cT
    cU
    @6
    @3
    @0
    @5
    cW
    cbs
    cfv
    #
    wss
    #
    @5
    @6
    wss
    @0
    @1
    @2
    simp1
    #
    @3
    cT
    cU
    @10
    @1
    @0
    cT
    @10
    wss
    @2
    cS
    cT
    @10
    cW
    @10
    eqid
    #
    lsmsp.s
    lssss
    3ad2ant2
    @2
    @0
    cU
    @10
    wss
    @1
    cS
    cU
    @10
    cW
    @13
    lsmsp.s
    lssss
    3ad2ant3
    unssd
    #
    @5
    cN
    @10
    cW
    @13
    lsmsp.n
    lspssid
    syl2anc
    #
    unssad
    @3
    cT
    cU
    @6
    @15
    unssbd
    @3
    cT
    cW
    csubg
    cfv
    #
    wcel
    #
    cU
    @16
    wcel
    #
    @6
    @16
    wcel
    @7
    @8
    wa
    @9
    wb
    @3
    cS
    @16
    cT
    @0
    @1
    cS
    @16
    wss
    @2
    cS
    cW
    lsmsp.s
    lsssssubg
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    sseldd
    #
    @3
    cS
    @16
    cU
    @19
    @0
    @1
    @2
    simp3
    sseldd
    #
    @3
    cS
    @16
    @6
    @19
    @3
    @0
    @11
    @6
    cS
    wcel
    @12
    @14
    cS
    @5
    cN
    @10
    cW
    @13
    lsmsp.s
    lsmsp.n
    lspcl
    syl2anc
    sseldd
    c.po
    cT
    cU
    @6
    cW
    lsmsp.p
    lsmlub
    syl3anc
    mpbi2and
    @3
    @0
    @4
    cS
    wcel
    @5
    @4
    wss
    #
    @6
    @4
    wss
    @12
    c.po
    cS
    cT
    cU
    cW
    lsmsp.s
    lsmsp.p
    lsmcl
    @3
    @17
    @18
    @22
    @20
    @21
    c.po
    cT
    cU
    cW
    lsmsp.p
    lsmunss
    syl2anc
    cS
    @5
    @4
    cN
    cW
    lsmsp.s
    lsmsp.n
    lspssp
    syl3anc
    eqssd
end
