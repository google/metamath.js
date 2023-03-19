include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "rddif.mm"
include "halfre.mm"
include "a1i.mm"
include "id.mm"
include "dnicld1.mm"
include "subge0d.mm"
include "mpbird.mm"

theorem rddif2
  let cA: class A


  assert |- ( A e. RR -> 0 <_ ( ( 1 / 2 ) - ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    c1
    c2
    cdiv
    co
    #
    cA
    @1
    caddc
    co
    cfl
    cfv
    cA
    cmin
    co
    cabs
    cfv
    #
    cmin
    co
    cle
    wbr
    @2
    @1
    cle
    wbr
    cA
    rddif
    @0
    @1
    @2
    @1
    cr
    wcel
    @0
    halfre
    a1i
    @0
    cA
    @0
    id
    dnicld1
    subge0d
    mpbird
end
