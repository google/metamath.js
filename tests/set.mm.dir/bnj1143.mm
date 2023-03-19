include "ciun.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "cab.mm"
include "df-iun.mm"
include "wn.mm"
include "wal.mm"
include "wex.mm"
include "notnotb.mm"
include "neq0.mm"
include "xchbinx.mm"
include "wa.mm"
include "df-rex.mm"
include "exsimpl.mm"
include "sylbi.mm"
include "con3i.mm"
include "alrimiv.mm"
include "eqeq1i.mm"
include "notbii.mm"
include "eleq2i.mm"
include "exbii.mm"
include "3bitr3i.mm"
include "alnex.mm"
include "abid.mm"
include "albii.mm"
include "3bitr2i.mm"
include "sylibr.mm"
include "syl5eq.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "wne.mm"
include "iunconst.mm"
include "eqimss.mm"
include "syl.mm"
include "pm2.61ine.mm"

theorem bnj1143
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  assert |- U_ x e. A B C_ B

  proof
    vx
    cA
    cB
    ciun
    #
    cB
    wss
    #
    cA
    c0
    cA
    c0
    wceq
    #
    @0
    c0
    cB
    @2
    @0
    vy
    cv
    cB
    wcel
    vx
    cA
    wrex
    vy
    cab
    #
    c0
    vx
    vy
    cA
    cB
    df-iun
    #
    @2
    vz
    cv
    #
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    wn
    #
    vz
    wal
    #
    @3
    c0
    wceq
    #
    @2
    @8
    vz
    @2
    vx
    cv
    cA
    wcel
    #
    vx
    wex
    #
    wn
    @8
    @2
    @2
    wn
    @12
    @2
    notnotb
    vx
    cA
    neq0
    xchbinx
    @7
    @12
    @7
    @11
    @6
    wa
    vx
    wex
    @12
    @6
    vx
    cA
    df-rex
    @11
    @6
    vx
    exsimpl
    sylbi
    con3i
    sylbi
    alrimiv
    @10
    @5
    @7
    vz
    cab
    #
    wcel
    #
    vz
    wex
    #
    wn
    @14
    wn
    #
    vz
    wal
    @9
    @10
    @10
    wn
    #
    @15
    @10
    notnotb
    @0
    c0
    wceq
    #
    wn
    @5
    @0
    wcel
    #
    vz
    wex
    @17
    @15
    vz
    @0
    neq0
    @18
    @10
    @0
    @3
    c0
    @4
    eqeq1i
    notbii
    @19
    @14
    vz
    @0
    @13
    @5
    vx
    vz
    cA
    cB
    df-iun
    eleq2i
    exbii
    3bitr3i
    xchbinx
    @14
    vz
    alnex
    @16
    @8
    vz
    @14
    @7
    @7
    vz
    abid
    notbii
    albii
    3bitr2i
    sylibr
    syl5eq
    cB
    0ss
    syl6eqss
    cA
    c0
    wne
    @0
    cB
    wceq
    @1
    vx
    cA
    cB
    iunconst
    @0
    cB
    eqimss
    syl
    pm2.61ine
end
