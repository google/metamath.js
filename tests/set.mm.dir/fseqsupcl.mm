include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "cr.mm"
include "wf.mm"
include "wa.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "wss.mm"
include "frn.mm"
include "adantl.mm"
include "cfn.mm"
include "c0.mm"
include "wne.mm"
include "wfo.mm"
include "fzfi.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "fofi.mm"
include "sylancr.mm"
include "cdm.mm"
include "wceq.mm"
include "fdm.mm"
include "simpl.mm"
include "fzn0.mm"
include "sylibr.mm"
include "eqnetrd.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "wor.mm"
include "w3a.mm"
include "ltso.mm"
include "fisupcl.mm"
include "mpan.mm"
include "syl3anc.mm"
include "sseldd.mm"

theorem fseqsupcl
  let cF: class F
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( N e. ( ZZ>= ` M ) /\ F : ( M ... N ) --> RR ) -> sup ( ran F , RR , < ) e. RR )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    #
    cM
    cN
    cfz
    co
    #
    cr
    cF
    wf
    #
    wa
    #
    cF
    crn
    #
    cr
    @4
    cr
    clt
    csup
    #
    @2
    @4
    cr
    wss
    #
    @0
    @1
    cr
    cF
    frn
    adantl
    #
    @3
    @4
    cfn
    wcel
    #
    @4
    c0
    wne
    #
    @6
    @5
    @4
    wcel
    #
    @3
    @1
    cfn
    wcel
    @1
    @4
    cF
    wfo
    #
    @8
    cM
    cN
    fzfi
    @3
    cF
    @1
    wfn
    #
    @11
    @2
    @12
    @0
    @1
    cr
    cF
    ffn
    adantl
    @1
    cF
    dffn4
    sylib
    @1
    @4
    cF
    fofi
    sylancr
    @3
    cF
    cdm
    #
    c0
    wne
    @9
    @3
    @13
    @1
    c0
    @2
    @13
    @1
    wceq
    @0
    @1
    cr
    cF
    fdm
    adantl
    @3
    @0
    @1
    c0
    wne
    @0
    @2
    simpl
    cM
    cN
    fzn0
    sylibr
    eqnetrd
    @13
    c0
    @4
    c0
    cF
    dm0rn0
    necon3bii
    sylib
    @7
    cr
    clt
    wor
    @8
    @9
    @6
    w3a
    @10
    ltso
    cr
    @4
    clt
    fisupcl
    mpan
    syl3anc
    sseldd
end
