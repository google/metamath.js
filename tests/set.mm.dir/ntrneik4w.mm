include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "wral.mm"
include "wcel.mm"
include "wb.mm"
include "cvv.mm"
include "wa.mm"
include "wal.mm"
include "dfcleq.mm"
include "eqcom.mm"
include "ralv.mm"
include "3bitr4i.mm"
include "wss.mm"
include "ssv.mm"
include "a1i.mm"
include "cdif.mm"
include "wn.mm"
include "vex.mm"
include "eldif.mm"
include "mpbiran.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrneiiex.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "elpwid.mm"
include "sseld.mm"
include "con3dimp.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "2falsed.mm"
include "ex.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "raldifeq.mm"
include "wbr.mm"
include "simpr.mm"
include "simplr.mm"
include "ntrneiel.mm"
include "bibi12d.mm"
include "ralbidva.mm"
include "bitr3d.mm"
include "syl5bb.mm"
include "ralcom.mm"
include "syl6bb.mm"

theorem ntrneik4w
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cI: class I
  let cN: class N
  let cO: class O
  let vs: setvar s
  let vl: setvar l
  assume ntrnei.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume ntrnei.f: |- F = ( ~P B O B )
  assume ntrnei.r: |- ( ph -> I F N )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B m
  disjoint B s
  disjoint B x
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i s
  disjoint i x
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint j s
  disjoint j x
  disjoint k l
  disjoint k m
  disjoint k s
  disjoint k x
  disjoint l m
  disjoint l s
  disjoint l x
  disjoint m s
  disjoint m x
  disjoint s x
  disjoint I k
  disjoint I l
  disjoint I m
  disjoint I x
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint ph s
  disjoint ph x
  assert |- ( ph -> ( A. s e. ~P B ( I ` ( I ` s ) ) = ( I ` s ) <-> A. x e. B A. s e. ~P B ( s e. ( N ` x ) <-> ( I ` s ) e. ( N ` x ) ) ) )

  proof
    wph
    vs
    cv
    #
    cI
    cfv
    #
    cI
    cfv
    #
    @1
    wceq
    #
    vs
    cB
    cpw
    #
    wral
    @0
    vx
    cv
    #
    cN
    cfv
    #
    wcel
    #
    @1
    @6
    wcel
    #
    wb
    #
    vx
    cB
    wral
    #
    vs
    @4
    wral
    @9
    vs
    @4
    wral
    vx
    cB
    wral
    wph
    @3
    @10
    vs
    @4
    @3
    @5
    @1
    wcel
    #
    @5
    @2
    wcel
    #
    wb
    #
    vx
    cvv
    wral
    #
    wph
    @0
    @4
    wcel
    #
    wa
    #
    @10
    @1
    @2
    wceq
    @13
    vx
    wal
    @3
    @14
    vx
    @1
    @2
    dfcleq
    @2
    @1
    eqcom
    @13
    vx
    ralv
    3bitr4i
    @16
    @13
    vx
    cB
    wral
    @14
    @10
    @16
    @13
    vx
    cB
    cvv
    cB
    cvv
    wss
    @16
    cB
    ssv
    a1i
    @16
    @13
    vx
    cvv
    cB
    cdif
    #
    @5
    @17
    wcel
    #
    @5
    cB
    wcel
    #
    wn
    #
    @16
    @13
    @18
    @5
    cvv
    wcel
    @20
    vx
    vex
    @5
    cvv
    cB
    eldif
    mpbiran
    @16
    @20
    @13
    @16
    @20
    wa
    @11
    @12
    @16
    @11
    @19
    @16
    @1
    cB
    @5
    @16
    @1
    cB
    wph
    @4
    @4
    @0
    cI
    wph
    cI
    @4
    @4
    cmap
    co
    wcel
    @4
    @4
    cI
    wf
    #
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
    @4
    @4
    elmapi
    syl
    #
    ffvelrnda
    #
    elpwid
    sseld
    con3dimp
    @16
    @12
    @19
    @16
    @2
    cB
    @5
    @16
    @2
    cB
    @16
    @4
    @4
    @1
    cI
    wph
    @21
    @15
    @22
    adantr
    @23
    ffvelrnd
    elpwid
    sseld
    con3dimp
    2falsed
    ex
    syl5bi
    ralrimiv
    raldifeq
    @16
    @13
    @9
    vx
    cB
    @16
    @19
    wa
    #
    @11
    @7
    @12
    @8
    @24
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
    @5
    vl
    ntrnei.o
    ntrnei.f
    @16
    cI
    cN
    cF
    wbr
    #
    @19
    wph
    @25
    @15
    ntrnei.r
    adantr
    adantr
    #
    @16
    @19
    simpr
    #
    wph
    @15
    @19
    simplr
    ntrneiel
    @24
    cB
    @1
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    @5
    vl
    ntrnei.o
    ntrnei.f
    @26
    @27
    @16
    @1
    @4
    wcel
    @19
    @23
    adantr
    ntrneiel
    bibi12d
    ralbidva
    bitr3d
    syl5bb
    ralbidva
    @9
    vs
    vx
    @4
    cB
    ralcom
    syl6bb
end
