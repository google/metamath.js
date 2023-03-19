include "ccusgr.mm"
include "wcel.mm"
include "cedg.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wi.mm"
include "eqid.mm"
include "cusgredg.mm"
include "wne.mm"
include "cpr.mm"
include "wa.mm"
include "wrex.mm"
include "fveq2.mm"
include "ad2antlr.mm"
include "wb.mm"
include "hashprg.mm"
include "adantrr.mm"
include "biimpcd.mm"
include "adantr.mm"
include "imp.mm"
include "eqtrd.mm"
include "an13s.mm"
include "rexlimdvaa.mm"
include "ss2rabdv.mm"
include "a1i.mm"
include "id.mm"
include "sseq12d.mm"
include "syl5ibr.mm"
include "syl.mm"

theorem cusgrfilem1
  let vx: setvar x
  let cP: class P
  let cG: class G
  let cN: class N
  let cV: class V
  let va: setvar a
  assume cusgrfi.v: |- V = ( Vtx ` G )
  assume cusgrfi.p: |- P = { x e. ~P V | E. a e. V ( a =/= N /\ x = { a , N } ) }

  disjoint G x
  disjoint N a
  disjoint N x
  disjoint a x
  disjoint V a
  disjoint V x
  assert |- ( ( G e. ComplUSGraph /\ N e. V ) -> P C_ ( Edg ` G ) )

  proof
    cG
    ccusgr
    wcel
    #
    cN
    cV
    wcel
    #
    cP
    cG
    cedg
    cfv
    #
    wss
    #
    @0
    @2
    vx
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    vx
    cV
    cpw
    #
    crab
    #
    wceq
    #
    @1
    @3
    wi
    vx
    @2
    cG
    cV
    cusgrfi.v
    @2
    eqid
    cusgredg
    @1
    @3
    @9
    va
    cv
    #
    cN
    wne
    #
    @4
    @10
    cN
    cpr
    #
    wceq
    #
    wa
    #
    va
    cV
    wrex
    #
    vx
    @7
    crab
    #
    @8
    wss
    @1
    @15
    @6
    vx
    @7
    @1
    @4
    @7
    wcel
    #
    wa
    #
    @14
    @6
    va
    cV
    @14
    @10
    cV
    wcel
    #
    @18
    @6
    @14
    @19
    @18
    wa
    #
    wa
    @5
    @12
    chash
    cfv
    #
    c2
    @13
    @5
    @21
    wceq
    @11
    @20
    @4
    @12
    chash
    fveq2
    ad2antlr
    @14
    @20
    @21
    c2
    wceq
    #
    @11
    @20
    @22
    wi
    @13
    @20
    @11
    @22
    @19
    @1
    @11
    @22
    wb
    @17
    @10
    cN
    cV
    cV
    hashprg
    adantrr
    biimpcd
    adantr
    imp
    eqtrd
    an13s
    rexlimdvaa
    ss2rabdv
    @9
    cP
    @16
    @2
    @8
    cP
    @16
    wceq
    @9
    cusgrfi.p
    a1i
    @9
    id
    sseq12d
    syl5ibr
    syl
    imp
end
