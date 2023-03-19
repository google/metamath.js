include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "sq11.mm"
include "syl22anc.mm"
include "mpbid.mm"

theorem sq11d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume resqcld.1: |- ( ph -> A e. RR )
  assume lt2sqd.2: |- ( ph -> B e. RR )
  assume lt2sqd.3: |- ( ph -> 0 <_ A )
  assume lt2sqd.4: |- ( ph -> 0 <_ B )
  assume sq11d.5: |- ( ph -> ( A ^ 2 ) = ( B ^ 2 ) )


  assert |- ( ph -> A = B )

  proof
    wph
    cA
    c2
    cexp
    co
    cB
    c2
    cexp
    co
    wceq
    #
    cA
    cB
    wceq
    #
    sq11d.5
    wph
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cB
    cr
    wcel
    cc0
    cB
    cle
    wbr
    @0
    @1
    wb
    resqcld.1
    lt2sqd.3
    lt2sqd.2
    lt2sqd.4
    cA
    cB
    sq11
    syl22anc
    mpbid
end
