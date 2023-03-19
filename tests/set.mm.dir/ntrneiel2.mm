include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "cab.mm"
include "wel.mm"
include "wb.mm"
include "wral.mm"
include "wrex.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrneiiex.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "ntrneiel.mm"
include "crab.mm"
include "ntrneifv4.mm"
include "df-rab.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "wal.mm"
include "wex.mm"
include "clabel.mm"
include "df-rex.mm"
include "bitr4i.mm"
include "cvv.mm"
include "ibar.mm"
include "bibi2d.mm"
include "ralbiia.mm"
include "wss.mm"
include "ssv.mm"
include "a1i.mm"
include "cdif.mm"
include "wn.mm"
include "vex.mm"
include "eldif.mm"
include "mpbiran.mm"
include "ntrneinex.mm"
include "elpwid.mm"
include "sselda.mm"
include "sseld.mm"
include "con3dimp.mm"
include "pm3.14.mm"
include "orcs.mm"
include "adantl.mm"
include "2falsed.mm"
include "ex.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "raldifeq.mm"
include "syl5bb.mm"
include "ralv.mm"
include "syl6rbb.mm"
include "rexbidva.mm"
include "3bitrd.mm"

theorem ntrneiel2
  let wph: wff ph
  let vy: setvar y
  let vu: setvar u
  let cB: class B
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cI: class I
  let cN: class N
  let cO: class O
  let cX: class X
  let vl: setvar l
  assume ntrnei.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume ntrnei.f: |- F = ( ~P B O B )
  assume ntrnei.r: |- ( ph -> I F N )
  assume ntrneiel2.x: |- ( ph -> X e. B )
  assume ntrneiel2.s: |- ( ph -> S e. ~P B )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B m
  disjoint B y
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i y
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint j y
  disjoint k l
  disjoint k m
  disjoint k y
  disjoint l m
  disjoint l y
  disjoint m y
  disjoint B u
  disjoint u y
  disjoint I k
  disjoint I l
  disjoint I m
  disjoint I y
  disjoint N u
  disjoint N y
  disjoint S m
  disjoint S y
  disjoint S u
  disjoint X l
  disjoint X m
  disjoint X y
  disjoint X u
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint ph y
  disjoint ph u
  assert |- ( ph -> ( X e. ( I ` ( I ` S ) ) <-> E. u e. ( N ` X ) A. y e. B ( y e. u <-> S e. ( N ` y ) ) ) )

  proof
    wph
    cX
    cS
    cI
    cfv
    #
    cI
    cfv
    wcel
    @0
    cX
    cN
    cfv
    #
    wcel
    vy
    cv
    #
    cB
    wcel
    #
    cS
    @2
    cN
    cfv
    wcel
    #
    wa
    #
    vy
    cab
    #
    @1
    wcel
    #
    vy
    vu
    wel
    #
    @4
    wb
    #
    vy
    cB
    wral
    #
    vu
    @1
    wrex
    #
    wph
    cB
    @0
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    cX
    vl
    ntrnei.o
    ntrnei.f
    ntrnei.r
    ntrneiel2.x
    wph
    cB
    cpw
    #
    @12
    cS
    cI
    wph
    cI
    @12
    @12
    cmap
    co
    wcel
    @12
    @12
    cI
    wf
    wph
    cB
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    vl
    ntrnei.o
    ntrnei.f
    ntrnei.r
    ntrneiiex
    cI
    @12
    @12
    elmapi
    syl
    ntrneiel2.s
    ffvelrnd
    ntrneiel
    wph
    @0
    @6
    @1
    wph
    @0
    @4
    vy
    cB
    crab
    @6
    wph
    vy
    cB
    cS
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    vl
    ntrnei.o
    ntrnei.f
    ntrnei.r
    ntrneiel2.s
    ntrneifv4
    @4
    vy
    cB
    df-rab
    syl6eq
    eleq1d
    @7
    @8
    @5
    wb
    #
    vy
    wal
    #
    vu
    @1
    wrex
    #
    wph
    @11
    @7
    vu
    cv
    #
    @1
    wcel
    #
    @14
    wa
    vu
    wex
    @15
    @5
    vy
    vu
    @1
    clabel
    @14
    vu
    @1
    df-rex
    bitr4i
    wph
    @14
    @10
    vu
    @1
    wph
    @17
    wa
    #
    @10
    @13
    vy
    cvv
    wral
    #
    @14
    @10
    @13
    vy
    cB
    wral
    @18
    @19
    @9
    @13
    vy
    cB
    @3
    @4
    @5
    @8
    @3
    @4
    ibar
    bibi2d
    ralbiia
    @18
    @13
    vy
    cB
    cvv
    cB
    cvv
    wss
    @18
    cB
    ssv
    a1i
    @18
    @13
    vy
    cvv
    cB
    cdif
    #
    @2
    @20
    wcel
    #
    @3
    wn
    #
    @18
    @13
    @21
    @2
    cvv
    wcel
    @22
    vy
    vex
    @2
    cvv
    cB
    eldif
    mpbiran
    @18
    @22
    @13
    @18
    @22
    wa
    @8
    @5
    @18
    @8
    @3
    @18
    @16
    cB
    @2
    @18
    @16
    cB
    wph
    @1
    @12
    @16
    wph
    @1
    @12
    wph
    cB
    @12
    cpw
    #
    cX
    cN
    wph
    cN
    @23
    cB
    cmap
    co
    wcel
    cB
    @23
    cN
    wf
    wph
    cB
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    vl
    ntrnei.o
    ntrnei.f
    ntrnei.r
    ntrneinex
    cN
    @23
    cB
    elmapi
    syl
    ntrneiel2.x
    ffvelrnd
    elpwid
    sselda
    elpwid
    sseld
    con3dimp
    @22
    @5
    wn
    #
    @18
    @22
    @4
    wn
    @24
    @3
    @4
    pm3.14
    orcs
    adantl
    2falsed
    ex
    syl5bi
    ralrimiv
    raldifeq
    syl5bb
    @13
    vy
    ralv
    syl6rbb
    rexbidva
    syl5bb
    3bitrd
end
