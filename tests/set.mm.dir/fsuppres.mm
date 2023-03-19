include "cres.mm"
include "cfsupp.mm"
include "wbr.mm"
include "csupp.mm"
include "co.mm"
include "cfn.mm"
include "wcel.mm"
include "wfun.mm"
include "wa.mm"
include "wi.mm"
include "fsuppimp.mm"
include "cvv.mm"
include "wss.mm"
include "relprcnfsupp.mm"
include "con4i.mm"
include "syl.mm"
include "jca.mm"
include "adantr.mm"
include "ressuppss.mm"
include "ssfi.mm"
include "expcom.mm"
include "3syl.mm"
include "com23.mm"
include "imp.mm"
include "mpcom.mm"
include "wb.mm"
include "funres.mm"
include "resexg.mm"
include "funisfsupp.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem fsuppres
  let wph: wff ph
  let cF: class F
  let cV: class V
  let cX: class X
  let cZ: class Z
  assume fsuppres.s: |- ( ph -> F finSupp Z )
  assume fsuppres.z: |- ( ph -> Z e. V )


  assert |- ( ph -> ( F |` X ) finSupp Z )

  proof
    wph
    cF
    cX
    cres
    #
    cZ
    cfsupp
    wbr
    #
    @0
    cZ
    csupp
    co
    #
    cfn
    wcel
    #
    cF
    cZ
    cfsupp
    wbr
    #
    wph
    @3
    fsuppres.s
    @4
    cF
    wfun
    #
    cF
    cZ
    csupp
    co
    #
    cfn
    wcel
    #
    wa
    #
    wph
    @3
    wi
    #
    cF
    cZ
    fsuppimp
    #
    @5
    @7
    @9
    @5
    wph
    @7
    @3
    wph
    @5
    @7
    @3
    wi
    #
    wph
    @5
    wa
    cF
    cvv
    wcel
    #
    cZ
    cV
    wcel
    #
    wa
    #
    @2
    @6
    wss
    #
    @11
    wph
    @14
    @5
    wph
    @12
    @13
    wph
    @4
    @12
    fsuppres.s
    @12
    @4
    cF
    cZ
    relprcnfsupp
    con4i
    #
    syl
    fsuppres.z
    jca
    adantr
    cX
    cF
    cvv
    cV
    cZ
    ressuppss
    @7
    @15
    @3
    @6
    @2
    ssfi
    expcom
    3syl
    expcom
    com23
    imp
    syl
    mpcom
    wph
    @0
    wfun
    #
    @0
    cvv
    wcel
    #
    @13
    @1
    @3
    wb
    wph
    @4
    @8
    @17
    fsuppres.s
    @10
    @5
    @17
    @7
    cX
    cF
    funres
    adantr
    3syl
    wph
    @4
    @12
    @18
    fsuppres.s
    @16
    cF
    cX
    cvv
    resexg
    3syl
    fsuppres.z
    @0
    cvv
    cV
    cZ
    funisfsupp
    syl3anc
    mpbird
end
