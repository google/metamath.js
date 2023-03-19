include "com.mm"
include "cuz.mm"
include "cfv.mm"
include "clt.mm"
include "coi.mm"
include "cdm.mm"
include "wceq.mm"
include "word.mm"
include "cep.mm"
include "wiso.mm"
include "wa.mm"
include "ordom.mm"
include "om2uzisoi.mm"
include "pm3.2i.mm"
include "wwe.mm"
include "wse.mm"
include "wb.mm"
include "ordwe.mm"
include "ax-mp.mm"
include "isowe.mm"
include "mpbi.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "exse.mm"
include "eqid.mm"
include "oieu.mm"
include "mp2an.mm"
include "simpri.mm"

theorem om2uzoi
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
  assert |- G = OrdIso ( < , ( ZZ>= ` C ) )

  proof
    com
    cC
    cuz
    cfv
    #
    clt
    coi
    #
    cdm
    wceq
    #
    cG
    @1
    wceq
    #
    com
    word
    #
    com
    @0
    cep
    clt
    cG
    wiso
    #
    wa
    #
    @2
    @3
    wa
    #
    @4
    @5
    ordom
    vx
    cC
    cG
    om2uz.1
    om2uz.2
    om2uzisoi
    #
    pm3.2i
    @0
    clt
    wwe
    #
    @0
    clt
    wse
    #
    @6
    @7
    wb
    com
    cep
    wwe
    #
    @9
    @4
    @11
    ordom
    com
    ordwe
    ax-mp
    @5
    @11
    @9
    wb
    @8
    com
    @0
    cep
    clt
    cG
    isowe
    ax-mp
    mpbi
    @0
    cvv
    wcel
    @10
    cC
    cuz
    fvex
    @0
    clt
    cvv
    exse
    ax-mp
    @0
    com
    clt
    @1
    cG
    @1
    eqid
    oieu
    mp2an
    mpbi
    simpri
end
