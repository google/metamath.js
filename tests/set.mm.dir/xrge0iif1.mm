include "c1.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "1elunit.mm"
include "cv.mm"
include "cpnf.mm"
include "clog.mm"
include "cneg.mm"
include "cif.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "fveq2.mm"
include "negeqd.mm"
include "log1.mm"
include "negeqi.mm"
include "neg0.mm"
include "eqtri.mm"
include "a1i.mm"
include "3eqtrd.mm"
include "c0ex.mm"
include "fvmpt.mm"
include "ax-mp.mm"

theorem xrge0iif1
  let vx: setvar x
  let cF: class F
  let cJ: class J
  let vy: setvar y
  let cX: class X
  let vw: setvar w
  let vz: setvar z
  let vu: setvar u
  let cY: class Y
  assume xrge0iifhmeo.1: |- F = ( x e. ( 0 [,] 1 ) |-> if ( x = 0 , +oo , -u ( log ` x ) ) )
  assume xrge0iifhmeo.k: |- J = ( ( ordTop ` <_ ) |`t ( 0 [,] +oo ) )

  disjoint F x
  disjoint x y
  disjoint X x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint u x
  disjoint Y x
  assert |- ( F ` 1 ) = 0

  proof
    c1
    cc0
    c1
    cicc
    co
    #
    wcel
    c1
    cF
    cfv
    cc0
    wceq
    1elunit
    vx
    c1
    vx
    cv
    #
    cc0
    wceq
    #
    cpnf
    @1
    clog
    cfv
    #
    cneg
    #
    cif
    #
    cc0
    @0
    cF
    @1
    c1
    wceq
    #
    @5
    @4
    c1
    clog
    cfv
    #
    cneg
    #
    cc0
    @6
    @2
    cpnf
    @4
    @6
    @1
    cc0
    @6
    @1
    cc0
    wne
    c1
    cc0
    wne
    ax-1ne0
    @1
    c1
    cc0
    neeq1
    mpbiri
    neneqd
    iffalsed
    @6
    @3
    @7
    @1
    c1
    clog
    fveq2
    negeqd
    @8
    cc0
    wceq
    @6
    @8
    cc0
    cneg
    cc0
    @7
    cc0
    log1
    negeqi
    neg0
    eqtri
    a1i
    3eqtrd
    xrge0iifhmeo.1
    c0ex
    fvmpt
    ax-mp
end
