include "cspths.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "cc0.mm"
include "wne.mm"
include "ctrls.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "wi.mm"
include "isspth.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf1.mm"
include "wcel.mm"
include "wceq.mm"
include "wf.mm"
include "cwlks.mm"
include "trliswlk.mm"
include "eqid.mm"
include "wlkp.mm"
include "syl.mm"
include "anim1i.mm"
include "df-f1.mm"
include "sylibr.mm"
include "cn0.mm"
include "wlkcl.mm"
include "nn0fz0.mm"
include "biimpi.mm"
include "0elfz.mm"
include "jca.mm"
include "3syl.mm"
include "adantr.mm"
include "eqcom.mm"
include "f1veqaeq.mm"
include "syl5bi.mm"
include "necon3d.mm"
include "sylbi.mm"
include "imp.mm"

theorem spthdep
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( ( F ( SPaths ` G ) P /\ ( # ` F ) =/= 0 ) -> ( P ` 0 ) =/= ( P ` ( # ` F ) ) )

  proof
    cF
    cP
    cG
    cspths
    cfv
    wbr
    #
    cF
    chash
    cfv
    #
    cc0
    wne
    #
    cc0
    cP
    cfv
    #
    @1
    cP
    cfv
    #
    wne
    #
    @0
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    #
    cP
    ccnv
    wfun
    #
    wa
    #
    @2
    @5
    wi
    cP
    cF
    cG
    isspth
    @8
    @3
    @4
    @1
    cc0
    @8
    cc0
    @1
    cfz
    co
    #
    cG
    cvtx
    cfv
    #
    cP
    wf1
    #
    @1
    @9
    wcel
    #
    cc0
    @9
    wcel
    #
    wa
    #
    wa
    #
    @3
    @4
    wceq
    #
    @1
    cc0
    wceq
    #
    wi
    @8
    @11
    @14
    @8
    @9
    @10
    cP
    wf
    #
    @7
    wa
    @11
    @6
    @18
    @7
    @6
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @18
    cP
    cF
    cG
    trliswlk
    #
    cP
    cF
    cG
    @10
    @10
    eqid
    wlkp
    syl
    anim1i
    @9
    @10
    cP
    df-f1
    sylibr
    @6
    @14
    @7
    @6
    @19
    @1
    cn0
    wcel
    #
    @14
    @20
    cP
    cF
    cG
    wlkcl
    @21
    @12
    @13
    @21
    @12
    @1
    nn0fz0
    biimpi
    @1
    0elfz
    jca
    3syl
    adantr
    jca
    @16
    @4
    @3
    wceq
    @15
    @17
    @3
    @4
    eqcom
    @9
    @10
    @1
    cc0
    cP
    f1veqaeq
    syl5bi
    syl
    necon3d
    sylbi
    imp
end
