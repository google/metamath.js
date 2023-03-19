include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "ltdiv2d.mm"
include "mpbid.mm"

theorem ltdiv2dd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltdiv2dd.a: |- ( ph -> A e. RR+ )
  assume ltdiv2dd.b: |- ( ph -> B e. RR+ )
  assume ltdiv2dd.c: |- ( ph -> C e. RR+ )
  assume ltdiv2dd.altb: |- ( ph -> A < B )


  assert |- ( ph -> ( C / B ) < ( C / A ) )

  proof
    wph
    cA
    cB
    clt
    wbr
    cC
    cB
    cdiv
    co
    cC
    cA
    cdiv
    co
    clt
    wbr
    ltdiv2dd.altb
    wph
    cA
    cB
    cC
    ltdiv2dd.a
    ltdiv2dd.b
    ltdiv2dd.c
    ltdiv2d
    mpbid
end
