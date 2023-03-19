include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "wf.mm"
include "wa.mm"
include "crn.mm"
include "cfv.mm"
include "wss.mm"
include "frn.mm"
include "adantl.mm"
include "cdm.mm"
include "wceq.mm"
include "c0.mm"
include "wne.mm"
include "fdm.mm"
include "ne0i.mm"
include "dm0rn0.mm"
include "eqeq1.mm"
include "biimpd.mm"
include "syl5bir.mm"
include "necon3d.mm"
include "mpan9.mm"
include "sylan2.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "fsequb2.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "ancoms.mm"
include "suprubd.mm"

theorem fseqsupubi
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( K e. ( M ... N ) /\ F : ( M ... N ) --> RR ) -> ( F ` K ) <_ sup ( ran F , RR , < ) )

  proof
    cK
    cM
    cN
    cfz
    co
    #
    wcel
    #
    @0
    cr
    cF
    wf
    #
    wa
    vx
    vy
    cF
    crn
    #
    cK
    cF
    cfv
    #
    @2
    @3
    cr
    wss
    @1
    @0
    cr
    cF
    frn
    adantl
    @2
    @1
    cF
    cdm
    #
    @0
    wceq
    #
    @3
    c0
    wne
    #
    @0
    cr
    cF
    fdm
    @1
    @0
    c0
    wne
    @6
    @7
    @0
    cK
    ne0i
    @6
    @3
    c0
    @0
    c0
    @3
    c0
    wceq
    @5
    c0
    wceq
    #
    @6
    @0
    c0
    wceq
    #
    cF
    dm0rn0
    @6
    @8
    @9
    @5
    @0
    c0
    eqeq1
    biimpd
    syl5bir
    necon3d
    mpan9
    sylan2
    @2
    vy
    cv
    vx
    cv
    cle
    wbr
    vy
    @3
    wral
    vx
    cr
    wrex
    @1
    vx
    vy
    cF
    cM
    cN
    fsequb2
    adantl
    @2
    @1
    cF
    @0
    wfn
    #
    @4
    @3
    wcel
    #
    @0
    cr
    cF
    ffn
    @10
    @1
    @11
    @0
    cK
    cF
    fnfvelrn
    ancoms
    sylan2
    suprubd
end
