include "cumgr.mm"
include "wcel.mm"
include "cpr.mm"
include "wa.mm"
include "cvtx.mm"
include "cfv.mm"
include "cpw.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "wne.mm"
include "cedg.mm"
include "eleq2i.mm"
include "edgumgr.mm"
include "sylan2b.mm"
include "eqid.mm"
include "hashprdifel.mm"
include "simp3d.mm"
include "adantl.mm"
include "syl.mm"

theorem umgredgne
  let cE: class E
  let cG: class G
  let cM: class M
  let cN: class N
  assume umgredgne.v: |- E = ( Edg ` G )


  assert |- ( ( G e. UMGraph /\ { M , N } e. E ) -> M =/= N )

  proof
    cG
    cumgr
    wcel
    #
    cM
    cN
    cpr
    #
    cE
    wcel
    #
    wa
    @1
    cG
    cvtx
    cfv
    cpw
    wcel
    #
    @1
    chash
    cfv
    c2
    wceq
    #
    wa
    #
    cM
    cN
    wne
    #
    @2
    @0
    @1
    cG
    cedg
    cfv
    #
    wcel
    @5
    cE
    @7
    @1
    umgredgne.v
    eleq2i
    @1
    cG
    edgumgr
    sylan2b
    @4
    @6
    @3
    @4
    cM
    @1
    wcel
    cN
    @1
    wcel
    @6
    cM
    cN
    @1
    @1
    eqid
    hashprdifel
    simp3d
    adantl
    syl
end
