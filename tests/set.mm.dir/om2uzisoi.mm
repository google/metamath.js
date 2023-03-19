include "com.mm"
include "cuz.mm"
include "cfv.mm"
include "cep.mm"
include "clt.mm"
include "wiso.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "wb.mm"
include "wral.mm"
include "om2uzf1oi.mm"
include "wcel.mm"
include "wa.mm"
include "epel.mm"
include "om2uzlt2i.mm"
include "syl5bb.mm"
include "rgen2a.mm"
include "df-isom.mm"
include "mpbir2an.mm"

theorem om2uzisoi
  let vx: setvar x
  let cC: class C
  let cG: class G
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  let cB: class B
  let vv: setvar v
  assume om2uz.1: |- C e. ZZ
  assume om2uz.2: |- G = ( rec ( ( x e. _V |-> ( x + 1 ) ) , C ) |` _om )

  disjoint C x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint C v
  disjoint w x
  disjoint w y
  disjoint C w
  disjoint x y
  disjoint x z
  disjoint C y
  disjoint C z
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint G z
  assert |- G Isom _E , < ( _om , ( ZZ>= ` C ) )

  proof
    com
    cC
    cuz
    cfv
    #
    cep
    clt
    cG
    wiso
    com
    @0
    cG
    wf1o
    vy
    cv
    #
    vz
    cv
    #
    cep
    wbr
    #
    @1
    cG
    cfv
    @2
    cG
    cfv
    clt
    wbr
    #
    wb
    #
    vz
    com
    wral
    vy
    com
    wral
    vx
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzf1oi
    @5
    vy
    vz
    com
    @3
    @1
    @2
    wcel
    @1
    com
    wcel
    @2
    com
    wcel
    wa
    @4
    vy
    vz
    epel
    vx
    @1
    @2
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzlt2i
    syl5bb
    rgen2a
    vy
    vz
    com
    @0
    cep
    clt
    cG
    df-isom
    mpbir2an
end
