include "cdif.mm"
include "cpw.mm"
include "wcel.mm"
include "wss.mm"
include "elpwid.mm"
include "ssdifssd.mm"
include "cvv.mm"
include "wb.mm"
include "difexg.mm"
include "elpwg.mm"
include "3syl.mm"
include "mpbird.mm"

theorem elpwdifcl
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume elpwincl.1: |- ( ph -> A e. ~P C )


  assert |- ( ph -> ( A \ B ) e. ~P C )

  proof
    wph
    cA
    cB
    cdif
    #
    cC
    cpw
    #
    wcel
    #
    @0
    cC
    wss
    #
    wph
    cA
    cC
    cB
    wph
    cA
    cC
    elpwincl.1
    elpwid
    ssdifssd
    wph
    cA
    @1
    wcel
    @0
    cvv
    wcel
    @2
    @3
    wb
    elpwincl.1
    cA
    cB
    @1
    difexg
    @0
    cC
    cvv
    elpwg
    3syl
    mpbird
end
