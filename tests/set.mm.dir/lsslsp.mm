include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfv.mm"
include "simp1.mm"
include "clss.mm"
include "wa.mm"
include "cbs.mm"
include "lsslmod.mm"
include "3adant3.mm"
include "simp3.mm"
include "wceq.mm"
include "eqid.mm"
include "lssss.mm"
include "3ad2ant2.mm"
include "ressbas2.mm"
include "syl.mm"
include "sseqtrd.mm"
include "lspcl.mm"
include "syl2anc.mm"
include "wb.mm"
include "lsslss.mm"
include "mpbid.mm"
include "simpld.mm"
include "lspssid.mm"
include "lspssp.mm"
include "syl3anc.mm"
include "sstrd.mm"
include "mpbir2and.mm"
include "eqssd.mm"

theorem lsslsp
  let cU: class U
  let cG: class G
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  assume lsslsp.x: |- X = ( W |`s U )
  assume lsslsp.m: |- M = ( LSpan ` W )
  assume lsslsp.n: |- N = ( LSpan ` X )
  assume lsslsp.l: |- L = ( LSubSp ` W )


  assert |- ( ( W e. LMod /\ U e. L /\ G C_ U ) -> ( M ` G ) = ( N ` G ) )

  proof
    cW
    clmod
    wcel
    #
    cU
    cL
    wcel
    #
    cG
    cU
    wss
    #
    w3a
    #
    cG
    cM
    cfv
    #
    cG
    cN
    cfv
    #
    @3
    @0
    @5
    cL
    wcel
    #
    cG
    @5
    wss
    #
    @4
    @5
    wss
    @0
    @1
    @2
    simp1
    #
    @3
    @6
    @5
    cU
    wss
    #
    @3
    @5
    cX
    clss
    cfv
    #
    wcel
    #
    @6
    @9
    wa
    #
    @3
    cX
    clmod
    wcel
    #
    cG
    cX
    cbs
    cfv
    #
    wss
    #
    @11
    @0
    @1
    @13
    @2
    cL
    cU
    cW
    cX
    lsslsp.x
    lsslsp.l
    lsslmod
    3adant3
    #
    @3
    cG
    cU
    @14
    @0
    @1
    @2
    simp3
    #
    @3
    cU
    cW
    cbs
    cfv
    #
    wss
    #
    cU
    @14
    wceq
    @1
    @0
    @19
    @2
    cL
    cU
    @18
    cW
    @18
    eqid
    #
    lsslsp.l
    lssss
    3ad2ant2
    #
    cU
    @18
    cX
    cW
    lsslsp.x
    @20
    ressbas2
    syl
    sseqtrd
    #
    @10
    cG
    cN
    @14
    cX
    @14
    eqid
    #
    @10
    eqid
    #
    lsslsp.n
    lspcl
    syl2anc
    @0
    @1
    @11
    @12
    wb
    @2
    cL
    @10
    cU
    @5
    cW
    cX
    lsslsp.x
    lsslsp.l
    @24
    lsslss
    3adant3
    mpbid
    simpld
    @3
    @13
    @15
    @7
    @16
    @22
    cG
    cN
    @14
    cX
    @23
    lsslsp.n
    lspssid
    syl2anc
    cL
    cG
    @5
    cM
    cW
    lsslsp.l
    lsslsp.m
    lspssp
    syl3anc
    @3
    @13
    @4
    @10
    wcel
    #
    cG
    @4
    wss
    #
    @5
    @4
    wss
    @16
    @3
    @25
    @4
    cL
    wcel
    #
    @4
    cU
    wss
    #
    @3
    @0
    cG
    @18
    wss
    #
    @27
    @8
    @3
    cG
    cU
    @18
    @17
    @21
    sstrd
    #
    cL
    cG
    cM
    @18
    cW
    @20
    lsslsp.l
    lsslsp.m
    lspcl
    syl2anc
    cL
    cG
    cU
    cM
    cW
    lsslsp.l
    lsslsp.m
    lspssp
    @0
    @1
    @25
    @27
    @28
    wa
    wb
    @2
    cL
    @10
    cU
    @4
    cW
    cX
    lsslsp.x
    lsslsp.l
    @24
    lsslss
    3adant3
    mpbir2and
    @3
    @0
    @29
    @26
    @8
    @30
    cG
    cM
    @18
    cW
    @20
    lsslsp.m
    lspssid
    syl2anc
    @10
    cG
    @4
    cN
    cX
    @24
    lsslsp.n
    lspssp
    syl3anc
    eqssd
end
