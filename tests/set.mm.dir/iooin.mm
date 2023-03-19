include "clt.mm"
include "cioo.mm"
include "df-ioo.mm"
include "cv.mm"
include "xrmaxlt.mm"
include "xrltmin.mm"
include "ixxin.mm"

theorem iooin
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( A e. RR* /\ B e. RR* ) /\ ( C e. RR* /\ D e. RR* ) ) -> ( ( A (,) B ) i^i ( C (,) D ) ) = ( if ( A <_ C , C , A ) (,) if ( B <_ D , B , D ) ) )

  proof
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    clt
    clt
    cioo
    vx
    vy
    vz
    df-ioo
    cA
    cC
    vz
    cv
    #
    xrmaxlt
    @0
    cB
    cD
    xrltmin
    ixxin
end
