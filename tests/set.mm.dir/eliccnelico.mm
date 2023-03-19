include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cxr.mm"
include "eliccxr.mm"
include "syl.mm"
include "cle.mm"
include "wbr.mm"
include "iccleub.mm"
include "syl3anc.mm"
include "cico.mm"
include "wn.mm"
include "wa.mm"
include "adantr.mm"
include "iccgelb.mm"
include "clt.mm"
include "simpr.mm"
include "wb.mm"
include "xrltnle.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "elicod.mm"
include "condan.mm"
include "xrletrid.mm"

theorem eliccnelico
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eliccnelico.1: |- ( ph -> A e. RR* )
  assume eliccnelico.b: |- ( ph -> B e. RR* )
  assume eliccnelico.c: |- ( ph -> C e. ( A [,] B ) )
  assume eliccnelico.nel: |- ( ph -> -. C e. ( A [,) B ) )


  assert |- ( ph -> C = B )

  proof
    wph
    cC
    cB
    wph
    cC
    cA
    cB
    cicc
    co
    wcel
    #
    cC
    cxr
    wcel
    #
    eliccnelico.c
    cC
    cA
    cB
    eliccxr
    syl
    #
    eliccnelico.b
    wph
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @0
    cC
    cB
    cle
    wbr
    eliccnelico.1
    eliccnelico.b
    eliccnelico.c
    cA
    cB
    cC
    iccleub
    syl3anc
    wph
    cB
    cC
    cle
    wbr
    #
    cC
    cA
    cB
    cico
    co
    wcel
    #
    wph
    @5
    wn
    #
    wa
    #
    cA
    cB
    cC
    wph
    @3
    @7
    eliccnelico.1
    adantr
    wph
    @4
    @7
    eliccnelico.b
    adantr
    wph
    @1
    @7
    @2
    adantr
    wph
    cA
    cC
    cle
    wbr
    #
    @7
    wph
    @3
    @4
    @0
    @9
    eliccnelico.1
    eliccnelico.b
    eliccnelico.c
    cA
    cB
    cC
    iccgelb
    syl3anc
    adantr
    @8
    cC
    cB
    clt
    wbr
    #
    @7
    wph
    @7
    simpr
    wph
    @10
    @7
    wb
    #
    @7
    wph
    @1
    @4
    @11
    @2
    eliccnelico.b
    cC
    cB
    xrltnle
    syl2anc
    adantr
    mpbird
    elicod
    wph
    @6
    wn
    @7
    eliccnelico.nel
    adantr
    condan
    xrletrid
end
