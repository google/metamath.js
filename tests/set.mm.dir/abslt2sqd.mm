include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wb.mm"
include "recnd.mm"
include "abscld.mm"
include "absge0d.mm"
include "lt2sq.mm"
include "syl22anc.mm"
include "mpbid.mm"
include "wceq.mm"
include "absresq.mm"
include "syl.mm"
include "breq12d.mm"

theorem abslt2sqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume abslt2sqd.a: |- ( ph -> A e. RR )
  assume abslt2sqd.b: |- ( ph -> B e. RR )
  assume abslt2sqd.l: |- ( ph -> ( abs ` A ) < ( abs ` B ) )


  assert |- ( ph -> ( A ^ 2 ) < ( B ^ 2 ) )

  proof
    wph
    cA
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cB
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    clt
    wbr
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    clt
    wbr
    wph
    @0
    @2
    clt
    wbr
    #
    @4
    abslt2sqd.l
    wph
    @0
    cr
    wcel
    cc0
    @0
    cle
    wbr
    @2
    cr
    wcel
    cc0
    @2
    cle
    wbr
    @7
    @4
    wb
    wph
    cA
    wph
    cA
    abslt2sqd.a
    recnd
    #
    abscld
    wph
    cA
    @8
    absge0d
    wph
    cB
    wph
    cB
    abslt2sqd.b
    recnd
    #
    abscld
    wph
    cB
    @9
    absge0d
    @0
    @2
    lt2sq
    syl22anc
    mpbid
    wph
    @1
    @5
    @3
    @6
    clt
    wph
    cA
    cr
    wcel
    @1
    @5
    wceq
    abslt2sqd.a
    cA
    absresq
    syl
    wph
    cB
    cr
    wcel
    @3
    @6
    wceq
    abslt2sqd.b
    cB
    absresq
    syl
    breq12d
    mpbid
end
