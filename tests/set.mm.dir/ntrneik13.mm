include "cv.mm"
include "cin.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "wss.mm"
include "wi.mm"
include "dfss3.mm"
include "wf.mm"
include "cmap.mm"
include "co.mm"
include "ntrneiiex.mm"
include "elmapi.mm"
include "syl.mm"
include "ad2antrr.mm"
include "cvv.mm"
include "ntrneibex.mm"
include "simplr.mm"
include "elpwi.mm"
include "ssinss1.mm"
include "3syl.mm"
include "sselpwd.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "ralss.mm"
include "syl5bb.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "anbi12d.mm"
include "eqss.mm"
include "ralbiim.mm"
include "3bitr4g.mm"
include "wbr.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "ntrneiel.mm"
include "elin.mm"
include "simpllr.mm"
include "bibi12d.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "ralcom.mm"
include "syl6bb.mm"

theorem ntrneik13
  let wph: wff ph
  let vx: setvar x
  let vt: setvar t
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
  disjoint B t
  disjoint B x
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i s
  disjoint i t
  disjoint i x
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint j s
  disjoint j t
  disjoint j x
  disjoint k l
  disjoint k m
  disjoint k s
  disjoint k t
  disjoint k x
  disjoint l m
  disjoint l s
  disjoint l t
  disjoint l x
  disjoint m s
  disjoint m t
  disjoint m x
  disjoint s t
  disjoint s x
  disjoint t x
  disjoint I k
  disjoint I l
  disjoint I m
  disjoint I x
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint ph s
  disjoint ph t
  disjoint ph x
  assert |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( I ` ( s i^i t ) ) = ( ( I ` s ) i^i ( I ` t ) ) <-> A. x e. B A. s e. ~P B A. t e. ~P B ( ( s i^i t ) e. ( N ` x ) <-> ( s e. ( N ` x ) /\ t e. ( N ` x ) ) ) ) )

  proof
    wph
    vs
    cv
    #
    vt
    cv
    #
    cin
    #
    cI
    cfv
    #
    @0
    cI
    cfv
    #
    @1
    cI
    cfv
    #
    cin
    #
    wceq
    #
    vt
    cB
    cpw
    #
    wral
    #
    vs
    @8
    wral
    @2
    vx
    cv
    #
    cN
    cfv
    #
    wcel
    #
    @0
    @11
    wcel
    #
    @1
    @11
    wcel
    #
    wa
    #
    wb
    #
    vt
    @8
    wral
    #
    vx
    cB
    wral
    #
    vs
    @8
    wral
    @17
    vs
    @8
    wral
    vx
    cB
    wral
    wph
    @9
    @18
    vs
    @8
    wph
    @0
    @8
    wcel
    #
    wa
    #
    @9
    @16
    vx
    cB
    wral
    #
    vt
    @8
    wral
    @18
    @20
    @7
    @21
    vt
    @8
    @20
    @1
    @8
    wcel
    #
    wa
    #
    @7
    @10
    @3
    wcel
    #
    @10
    @6
    wcel
    #
    wb
    #
    vx
    cB
    wral
    #
    @21
    @23
    @3
    @6
    wss
    #
    @6
    @3
    wss
    #
    wa
    @24
    @25
    wi
    vx
    cB
    wral
    #
    @25
    @24
    wi
    vx
    cB
    wral
    #
    wa
    @7
    @27
    @23
    @28
    @30
    @29
    @31
    @28
    @25
    vx
    @3
    wral
    #
    @23
    @30
    vx
    @3
    @6
    dfss3
    @23
    @3
    cB
    wss
    @32
    @30
    wb
    @23
    @3
    cB
    @23
    @8
    @8
    @2
    cI
    wph
    @8
    @8
    cI
    wf
    #
    @19
    @22
    wph
    cI
    @8
    @8
    cmap
    co
    wcel
    @33
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
    @8
    @8
    elmapi
    syl
    #
    ad2antrr
    @23
    @2
    cB
    cvv
    wph
    cB
    cvv
    wcel
    #
    @19
    @22
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
    ntrneibex
    #
    ad2antrr
    @23
    @19
    @0
    cB
    wss
    #
    @2
    cB
    wss
    #
    wph
    @19
    @22
    simplr
    @0
    cB
    elpwi
    @0
    @1
    cB
    ssinss1
    #
    3syl
    sselpwd
    ffvelrnd
    elpwid
    @25
    vx
    @3
    cB
    ralss
    syl
    syl5bb
    @29
    @24
    vx
    @6
    wral
    #
    @23
    @31
    vx
    @6
    @3
    dfss3
    @23
    @6
    cB
    wss
    #
    @40
    @31
    wb
    @20
    @41
    @22
    @20
    @4
    cB
    wss
    @41
    @20
    @4
    cB
    wph
    @8
    @8
    @0
    cI
    @34
    ffvelrnda
    elpwid
    @4
    @5
    cB
    ssinss1
    syl
    adantr
    @24
    vx
    @6
    cB
    ralss
    syl
    syl5bb
    anbi12d
    @3
    @6
    eqss
    @24
    @25
    vx
    cB
    ralbiim
    3bitr4g
    @23
    @26
    @16
    vx
    cB
    @23
    @10
    cB
    wcel
    #
    wa
    #
    @24
    @12
    @25
    @15
    @43
    cB
    @2
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    @10
    vl
    ntrnei.o
    ntrnei.f
    wph
    cI
    cN
    cF
    wbr
    @19
    @22
    @42
    ntrnei.r
    ad3antrrr
    #
    @23
    @42
    simpr
    #
    @20
    @2
    @8
    wcel
    @22
    @42
    @20
    @2
    cB
    cvv
    wph
    @35
    @19
    @36
    adantr
    @20
    @37
    @38
    @20
    @0
    cB
    wph
    @19
    simpr
    elpwid
    @39
    syl
    sselpwd
    ad2antrr
    ntrneiel
    @25
    @10
    @4
    wcel
    #
    @10
    @5
    wcel
    #
    wa
    @43
    @15
    @10
    @4
    @5
    elin
    @43
    @46
    @13
    @47
    @14
    @43
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
    @10
    vl
    ntrnei.o
    ntrnei.f
    @44
    @45
    wph
    @19
    @22
    @42
    simpllr
    ntrneiel
    @43
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
    @10
    vl
    ntrnei.o
    ntrnei.f
    @44
    @45
    @20
    @22
    @42
    simplr
    ntrneiel
    anbi12d
    syl5bb
    bibi12d
    ralbidva
    bitrd
    ralbidva
    @16
    vt
    vx
    @8
    cB
    ralcom
    syl6bb
    ralbidva
    @17
    vs
    vx
    @8
    cB
    ralcom
    syl6bb
end
