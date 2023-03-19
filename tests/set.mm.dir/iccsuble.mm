include "cr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "eliccre.mm"
include "syl3anc.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp3d.mm"
include "simp2d.mm"
include "le2subd.mm"

theorem iccsuble
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume iccsuble.1: |- ( ph -> A e. RR )
  assume iccsuble.2: |- ( ph -> B e. RR )
  assume iccsuble.3: |- ( ph -> C e. ( A [,] B ) )
  assume iccsuble.4: |- ( ph -> D e. ( A [,] B ) )


  assert |- ( ph -> ( C - D ) <_ ( B - A ) )

  proof
    wph
    cC
    cA
    cB
    cD
    wph
    cA
    cr
    wcel
    #
    cB
    cr
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
    cr
    wcel
    #
    iccsuble.1
    iccsuble.2
    iccsuble.3
    cA
    cB
    cC
    eliccre
    syl3anc
    iccsuble.1
    iccsuble.2
    wph
    @0
    @1
    cD
    @2
    wcel
    #
    cD
    cr
    wcel
    #
    iccsuble.1
    iccsuble.2
    iccsuble.4
    cA
    cB
    cD
    eliccre
    syl3anc
    wph
    @4
    cA
    cC
    cle
    wbr
    #
    cC
    cB
    cle
    wbr
    #
    wph
    @3
    @4
    @7
    @8
    w3a
    #
    iccsuble.3
    wph
    @0
    @1
    @3
    @9
    wb
    iccsuble.1
    iccsuble.2
    cA
    cB
    cC
    elicc2
    syl2anc
    mpbid
    simp3d
    wph
    @6
    cA
    cD
    cle
    wbr
    #
    cD
    cB
    cle
    wbr
    #
    wph
    @5
    @6
    @10
    @11
    w3a
    #
    iccsuble.4
    wph
    @0
    @1
    @5
    @12
    wb
    iccsuble.1
    iccsuble.2
    cA
    cB
    cD
    elicc2
    syl2anc
    mpbid
    simp2d
    le2subd
end
