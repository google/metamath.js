include "cioc.mm"
include "co.mm"
include "wcel.mm"
include "cicc.mm"
include "wne.mm"
include "wa.mm"
include "iocssicc.mm"
include "sseli.mm"
include "adantl.mm"
include "cr.mm"
include "adantr.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "rexrd.mm"
include "simpr.mm"
include "iocgtlb.mm"
include "syl3anc.mm"
include "gtned.mm"
include "jca.mm"
include "iccssred.mm"
include "sselda.mm"
include "adantrr.mm"
include "cle.mm"
include "iccgelb.mm"
include "simprr.mm"
include "leneltd.mm"
include "iccleub.mm"
include "eliocd.mm"
include "impbida.mm"

theorem eliccelioc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eliccelioc.a: |- ( ph -> A e. RR )
  assume eliccelioc.b: |- ( ph -> B e. RR )
  assume eliccelioc.c: |- ( ph -> C e. RR* )


  assert |- ( ph -> ( C e. ( A (,] B ) <-> ( C e. ( A [,] B ) /\ C =/= A ) ) )

  proof
    wph
    cC
    cA
    cB
    cioc
    co
    #
    wcel
    #
    cC
    cA
    cB
    cicc
    co
    #
    wcel
    #
    cC
    cA
    wne
    #
    wa
    #
    wph
    @1
    wa
    #
    @3
    @4
    @1
    @3
    wph
    @0
    @2
    cC
    cA
    cB
    iocssicc
    sseli
    adantl
    @6
    cA
    cC
    wph
    cA
    cr
    wcel
    #
    @1
    eliccelioc.a
    adantr
    @6
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @1
    cA
    cC
    clt
    wbr
    wph
    @8
    @1
    wph
    cA
    eliccelioc.a
    rexrd
    #
    adantr
    @6
    cB
    wph
    cB
    cr
    wcel
    @1
    eliccelioc.b
    adantr
    rexrd
    wph
    @1
    simpr
    cA
    cB
    cC
    iocgtlb
    syl3anc
    gtned
    jca
    wph
    @5
    wa
    #
    cA
    cB
    cC
    wph
    @8
    @5
    @10
    adantr
    wph
    @9
    @5
    wph
    cB
    eliccelioc.b
    rexrd
    #
    adantr
    wph
    cC
    cxr
    wcel
    @5
    eliccelioc.c
    adantr
    @11
    cA
    cC
    wph
    @7
    @5
    eliccelioc.a
    adantr
    wph
    @3
    cC
    cr
    wcel
    @4
    wph
    @2
    cr
    cC
    wph
    cA
    cB
    eliccelioc.a
    eliccelioc.b
    iccssred
    sselda
    adantrr
    wph
    @3
    cA
    cC
    cle
    wbr
    #
    @4
    wph
    @3
    wa
    #
    @8
    @9
    @3
    @13
    wph
    @8
    @3
    @10
    adantr
    #
    wph
    @9
    @3
    @12
    adantr
    #
    wph
    @3
    simpr
    #
    cA
    cB
    cC
    iccgelb
    syl3anc
    adantrr
    wph
    @3
    @4
    simprr
    leneltd
    wph
    @3
    cC
    cB
    cle
    wbr
    #
    @4
    @14
    @8
    @9
    @3
    @18
    @15
    @16
    @17
    cA
    cB
    cC
    iccleub
    syl3anc
    adantrr
    eliocd
    impbida
end
