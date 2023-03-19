include "crn.mm"
include "cres.mm"
include "wfn.mm"
include "wa.mm"
include "ccom.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "fnfun.mm"
include "funresfunco.mm"
include "syl2an.mm"
include "wss.mm"
include "fndm.mm"
include "cin.mm"
include "dmres.mm"
include "eqeq1i.mm"
include "df-ss.mm"
include "sylbb2.mm"
include "syl.mm"
include "adantr.mm"
include "dmcosseq.mm"
include "adantl.mm"
include "eqtrd.mm"
include "df-fn.mm"
include "sylanbrc.mm"

theorem fnresfnco
  let cB: class B
  let cF: class F
  let cG: class G
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( ( F |` ran G ) Fn ran G /\ G Fn B ) -> ( F o. G ) Fn B )

  proof
    cF
    cG
    crn
    #
    cres
    #
    @0
    wfn
    #
    cG
    cB
    wfn
    #
    wa
    #
    cF
    cG
    ccom
    #
    wfun
    #
    @5
    cdm
    #
    cB
    wceq
    @5
    cB
    wfn
    @2
    @1
    wfun
    cG
    wfun
    @6
    @3
    @0
    @1
    fnfun
    cB
    cG
    fnfun
    cF
    cG
    funresfunco
    syl2an
    @4
    @7
    cG
    cdm
    #
    cB
    @4
    @0
    cF
    cdm
    #
    wss
    #
    @7
    @8
    wceq
    @2
    @10
    @3
    @2
    @1
    cdm
    #
    @0
    wceq
    #
    @10
    @0
    @1
    fndm
    @12
    @0
    @9
    cin
    #
    @0
    wceq
    @10
    @11
    @13
    @0
    cF
    @0
    dmres
    eqeq1i
    @0
    @9
    df-ss
    sylbb2
    syl
    adantr
    cF
    cG
    dmcosseq
    syl
    @3
    @8
    cB
    wceq
    @2
    cB
    cG
    fndm
    adantl
    eqtrd
    @5
    cB
    df-fn
    sylanbrc
end
