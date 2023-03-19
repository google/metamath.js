include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "cpws.mm"
include "ccrg.mm"
include "cvv.mm"
include "eqcomi.mm"
include "oveq1i.mm"
include "oveq2i.mm"
include "eqid.mm"
include "csubrg.mm"
include "mpfrcl.mm"
include "simp2d.mm"
include "ovexd.mm"
include "w3a.mm"
include "wss.mm"
include "mpfsubrg.mm"
include "subrgss.mm"
include "3syl.mm"
include "id.mm"
include "sseldd.mm"
include "pwselbas.mm"

theorem mpff
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cF: class F
  let cI: class I
  assume mpfsubrg.q: |- Q = ran ( ( I evalSub S ) ` R )
  assume mpff.b: |- B = ( Base ` S )


  assert |- ( F e. Q -> F : ( B ^m I ) --> B )

  proof
    cF
    cQ
    wcel
    #
    cB
    cS
    cB
    cI
    cmap
    co
    #
    cS
    cS
    cbs
    cfv
    #
    cI
    cmap
    co
    #
    cpws
    co
    #
    cbs
    cfv
    #
    ccrg
    cF
    @4
    cvv
    @3
    @1
    cS
    cpws
    @2
    cB
    cI
    cmap
    cB
    @2
    mpff.b
    eqcomi
    oveq1i
    oveq2i
    mpff.b
    @5
    eqid
    #
    @0
    cI
    cvv
    wcel
    #
    cS
    ccrg
    wcel
    #
    cR
    cS
    csubrg
    cfv
    wcel
    #
    cQ
    cR
    cS
    cI
    cF
    mpfsubrg.q
    mpfrcl
    #
    simp2d
    @0
    cB
    cI
    cmap
    ovexd
    @0
    cQ
    @5
    cF
    @0
    @7
    @8
    @9
    w3a
    cQ
    @4
    csubrg
    cfv
    wcel
    cQ
    @5
    wss
    @10
    cQ
    cR
    cS
    cI
    cvv
    mpfsubrg.q
    mpfsubrg
    cQ
    @5
    @4
    @6
    subrgss
    3syl
    @0
    id
    sseldd
    pwselbas
end
