include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "breqtrd.mm"
include "lesubaddd.mm"
include "mpbird.mm"

theorem int-ineqmvtd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume int-ineqmvtd.1: |- ( ph -> B e. RR )
  assume int-ineqmvtd.2: |- ( ph -> C e. RR )
  assume int-ineqmvtd.3: |- ( ph -> D e. RR )
  assume int-ineqmvtd.4: |- ( ph -> B <_ A )
  assume int-ineqmvtd.5: |- ( ph -> A = ( C + D ) )


  assert |- ( ph -> ( B - D ) <_ C )

  proof
    wph
    cB
    cD
    cmin
    co
    cC
    cle
    wbr
    cB
    cC
    cD
    caddc
    co
    #
    cle
    wbr
    wph
    cB
    cA
    @0
    cle
    int-ineqmvtd.4
    int-ineqmvtd.5
    breqtrd
    wph
    cB
    cD
    cC
    int-ineqmvtd.1
    int-ineqmvtd.3
    int-ineqmvtd.2
    lesubaddd
    mpbird
end
