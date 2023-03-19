include "wel.mm"
include "cv.mm"
include "wne.mm"
include "wa.mm"
include "wn.mm"
include "csn.mm"
include "cdif.mm"
include "cuni.mm"
include "wral.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "eleq1.mm"
include "neeq2.mm"
include "anbi12d.mm"
include "elequ2.mm"
include "notbid.mm"
include "imbi12d.mm"
include "spv.mm"
include "eldif.mm"
include "simpr.mm"
include "wex.mm"
include "eluni.mm"
include "notbii.mm"
include "alnex.mm"
include "con2b.mm"
include "imnan.mm"
include "eldifsn.mm"
include "necom.mm"
include "anbi2i.mm"
include "bitri.mm"
include "imbi1i.mm"
include "3bitr3i.mm"
include "albii.mm"
include "3bitr2i.mm"
include "sylib.mm"
include "sylbi.mm"
include "syl11.mm"
include "ralrimiv.mm"
include "disj.mm"
include "sylibr.mm"

theorem kmlem4
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let vv: setvar v
  let vu: setvar u
  let vy: setvar y
  let wph: wff ph
  let wps: wff ps

  disjoint w x
  disjoint w z
  disjoint x z
  disjoint A v
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint ph u
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint ps x
  disjoint ps v
  disjoint u w
  disjoint u z
  disjoint v w
  disjoint v z
  disjoint w y
  disjoint y z
  assert |- ( ( w e. x /\ z =/= w ) -> ( ( z \ U. ( x \ { z } ) ) i^i w ) = (/) )

  proof
    vw
    vx
    wel
    #
    vz
    cv
    #
    vw
    cv
    #
    wne
    #
    wa
    #
    vy
    vw
    wel
    #
    wn
    #
    vy
    @1
    vx
    cv
    #
    @1
    csn
    cdif
    #
    cuni
    #
    cdif
    #
    wral
    @10
    @2
    cin
    c0
    wceq
    @4
    @6
    vy
    @10
    vv
    vx
    wel
    #
    @1
    vv
    cv
    #
    wne
    #
    wa
    #
    vy
    vv
    wel
    #
    wn
    #
    wi
    #
    vv
    wal
    #
    @4
    @6
    vy
    cv
    #
    @10
    wcel
    #
    @17
    @4
    @6
    wi
    vv
    vw
    @12
    @2
    wceq
    #
    @14
    @4
    @16
    @6
    @21
    @11
    @0
    @13
    @3
    @12
    @2
    @7
    eleq1
    @12
    @2
    @1
    neeq2
    anbi12d
    @21
    @15
    @5
    vv
    vw
    vy
    elequ2
    notbid
    imbi12d
    spv
    @20
    vy
    vz
    wel
    #
    @19
    @9
    wcel
    #
    wn
    #
    wa
    #
    @18
    @19
    @1
    @9
    eldif
    @25
    @24
    @18
    @22
    @24
    simpr
    @24
    @15
    @12
    @8
    wcel
    #
    wa
    #
    vv
    wex
    #
    wn
    @27
    wn
    #
    vv
    wal
    @18
    @23
    @28
    vv
    @19
    @8
    eluni
    notbii
    @27
    vv
    alnex
    @29
    @17
    vv
    @15
    @26
    wn
    wi
    @26
    @16
    wi
    @29
    @17
    @15
    @26
    con2b
    @15
    @26
    imnan
    @26
    @14
    @16
    @26
    @11
    @12
    @1
    wne
    #
    wa
    @14
    @12
    @7
    @1
    eldifsn
    @30
    @13
    @11
    @12
    @1
    necom
    anbi2i
    bitri
    imbi1i
    3bitr3i
    albii
    3bitr2i
    sylib
    sylbi
    syl11
    ralrimiv
    vy
    @10
    @2
    disj
    sylibr
end
