include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "caddc.mm"
include "wne.mm"
include "wa.mm"
include "cfv.mm"
include "cop.mm"
include "csn.mm"
include "cdif.mm"
include "cc0.mm"
include "cxp.mm"
include "cun.mm"
include "fveq1i.mm"
include "wceq.mm"
include "eldifsn.mm"
include "cin.mm"
include "c0.mm"
include "disjdif.mm"
include "wfn.mm"
include "ovex.mm"
include "1ex.mm"
include "fnsn.mm"
include "wf.mm"
include "c0ex.mm"
include "fconst.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fvun2.mm"
include "mp3an12.mm"
include "mpan.mm"
include "fvconst2.mm"
include "eqtrd.mm"
include "sylbir.mm"
include "syl5eq.mm"

theorem axlowdimlem12
  let cQ: class Q
  let cI: class I
  let cK: class K
  let cN: class N
  assume axlowdimlem10.1: |- Q = ( { <. ( I + 1 ) , 1 >. } u. ( ( ( 1 ... N ) \ { ( I + 1 ) } ) X. { 0 } ) )


  assert |- ( ( K e. ( 1 ... N ) /\ K =/= ( I + 1 ) ) -> ( Q ` K ) = 0 )

  proof
    cK
    c1
    cN
    cfz
    co
    #
    wcel
    cK
    cI
    c1
    caddc
    co
    #
    wne
    wa
    #
    cK
    cQ
    cfv
    cK
    @1
    c1
    cop
    csn
    #
    @0
    @1
    csn
    #
    cdif
    #
    cc0
    csn
    #
    cxp
    #
    cun
    #
    cfv
    #
    cc0
    cK
    cQ
    @8
    axlowdimlem10.1
    fveq1i
    @2
    cK
    @5
    wcel
    #
    @9
    cc0
    wceq
    cK
    @0
    @1
    eldifsn
    @10
    @9
    cK
    @7
    cfv
    #
    cc0
    @4
    @5
    cin
    c0
    wceq
    #
    @10
    @9
    @11
    wceq
    #
    @4
    @0
    disjdif
    @3
    @4
    wfn
    @7
    @5
    wfn
    #
    @12
    @10
    wa
    @13
    @1
    c1
    cI
    c1
    caddc
    ovex
    1ex
    fnsn
    @5
    @6
    @7
    wf
    @14
    @5
    cc0
    c0ex
    fconst
    @5
    @6
    @7
    ffn
    ax-mp
    @4
    @5
    @3
    @7
    cK
    fvun2
    mp3an12
    mpan
    @5
    cc0
    cK
    c0ex
    fvconst2
    eqtrd
    sylbir
    syl5eq
end
