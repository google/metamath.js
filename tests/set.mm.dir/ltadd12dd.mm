include "caddc.mm"
include "co.mm"
include "readdcld.mm"
include "ltadd1dd.mm"
include "ltadd2dd.mm"
include "lttrd.mm"

theorem ltadd12dd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ltadd12dd.a: |- ( ph -> A e. RR )
  assume ltadd12dd.b: |- ( ph -> B e. RR )
  assume ltadd12dd.c: |- ( ph -> C e. RR )
  assume ltadd12dd.d: |- ( ph -> D e. RR )
  assume ltadd12dd.ac: |- ( ph -> A < C )
  assume ltadd12dd.bd: |- ( ph -> B < D )


  assert |- ( ph -> ( A + B ) < ( C + D ) )

  proof
    wph
    cA
    cB
    caddc
    co
    cC
    cB
    caddc
    co
    cC
    cD
    caddc
    co
    wph
    cA
    cB
    ltadd12dd.a
    ltadd12dd.b
    readdcld
    wph
    cC
    cB
    ltadd12dd.c
    ltadd12dd.b
    readdcld
    wph
    cC
    cD
    ltadd12dd.c
    ltadd12dd.d
    readdcld
    wph
    cA
    cC
    cB
    ltadd12dd.a
    ltadd12dd.c
    ltadd12dd.b
    ltadd12dd.ac
    ltadd1dd
    wph
    cB
    cD
    cC
    ltadd12dd.b
    ltadd12dd.d
    ltadd12dd.c
    ltadd12dd.bd
    ltadd2dd
    lttrd
end
