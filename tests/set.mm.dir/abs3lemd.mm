include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cc.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "wi.mm"
include "abs3lem.mm"
include "syl22anc.mm"
include "mp2and.mm"

theorem abs3lemd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume abscld.1: |- ( ph -> A e. CC )
  assume abssubd.2: |- ( ph -> B e. CC )
  assume abs3difd.3: |- ( ph -> C e. CC )
  assume abs3lemd.4: |- ( ph -> D e. RR )
  assume abs3lemd.5: |- ( ph -> ( abs ` ( A - C ) ) < ( D / 2 ) )
  assume abs3lemd.6: |- ( ph -> ( abs ` ( C - B ) ) < ( D / 2 ) )


  assert |- ( ph -> ( abs ` ( A - B ) ) < D )

  proof
    wph
    cA
    cC
    cmin
    co
    cabs
    cfv
    cD
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    cC
    cB
    cmin
    co
    cabs
    cfv
    @0
    clt
    wbr
    #
    cA
    cB
    cmin
    co
    cabs
    cfv
    cD
    clt
    wbr
    #
    abs3lemd.5
    abs3lemd.6
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cc
    wcel
    cD
    cr
    wcel
    @1
    @2
    wa
    @3
    wi
    abscld.1
    abssubd.2
    abs3difd.3
    abs3lemd.4
    cA
    cB
    cC
    cD
    abs3lem
    syl22anc
    mp2and
end
