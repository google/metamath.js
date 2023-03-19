include "wcel.mm"
include "c0.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "ciedg.mm"
include "cdm.mm"
include "cword.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "iswlkg.mm"
include "wa.mm"
include "ral0.mm"
include "hash0.mm"
include "oveq2i.mm"
include "fzo0.mm"
include "eqtri.mm"
include "raleqi.mm"
include "mpbir.mm"
include "biantru.mm"
include "eqcomi.mm"
include "feq2i.mm"
include "wrd0.mm"
include "biantrur.mm"
include "bitri.mm"
include "df-3an.mm"
include "3bitr4ri.mm"
include "syl6bb.mm"

theorem 0wlk
  let cP: class P
  let cU: class U
  let cG: class G
  let cV: class V
  let vk: setvar k
  assume 0wlk.v: |- V = ( Vtx ` G )


  assert |- ( G e. U -> ( (/) ( Walks ` G ) P <-> P : ( 0 ... 0 ) --> V ) )

  proof
    cG
    cU
    wcel
    c0
    cP
    cG
    cwlks
    cfv
    wbr
    c0
    cG
    ciedg
    cfv
    #
    cdm
    #
    cword
    wcel
    #
    cc0
    c0
    chash
    cfv
    #
    cfz
    co
    #
    cV
    cP
    wf
    #
    vk
    cv
    #
    cP
    cfv
    #
    @6
    c1
    caddc
    co
    cP
    cfv
    #
    wceq
    @6
    c0
    cfv
    @0
    cfv
    #
    @7
    csn
    wceq
    @7
    @8
    cpr
    @9
    wss
    wif
    #
    vk
    cc0
    @3
    cfzo
    co
    #
    wral
    #
    w3a
    #
    cc0
    cc0
    cfz
    co
    #
    cV
    cP
    wf
    #
    cP
    vk
    c0
    cG
    @0
    cV
    cU
    0wlk.v
    @0
    eqid
    iswlkg
    @2
    @5
    wa
    #
    @16
    @12
    wa
    @15
    @13
    @12
    @16
    @12
    @10
    vk
    c0
    wral
    @10
    vk
    ral0
    @10
    vk
    @11
    c0
    @11
    cc0
    cc0
    cfzo
    co
    c0
    @3
    cc0
    cc0
    cfzo
    hash0
    oveq2i
    cc0
    fzo0
    eqtri
    raleqi
    mpbir
    biantru
    @15
    @5
    @16
    @14
    @4
    cV
    cP
    cc0
    @3
    cc0
    cfz
    @3
    cc0
    hash0
    eqcomi
    oveq2i
    feq2i
    @2
    @5
    @1
    wrd0
    biantrur
    bitri
    @2
    @5
    @12
    df-3an
    3bitr4ri
    syl6bb
end
