include "cv.mm"
include "cun.mm"
include "cfv.mm"
include "wceq.mm"
include "cpw.mm"
include "wral.mm"
include "wcel.mm"
include "wo.mm"
include "wb.mm"
include "wa.mm"
include "wss.mm"
include "wi.mm"
include "dfss3.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrneiiex.mm"
include "ad2antrr.mm"
include "elmapi.mm"
include "syl.mm"
include "cvv.mm"
include "ntrneibex.mm"
include "simplr.mm"
include "elpwid.mm"
include "simpr.mm"
include "unssd.mm"
include "sselpwd.mm"
include "ffvelrnd.mm"
include "ralss.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "eqss.mm"
include "ralbiim.mm"
include "3bitr4g.mm"
include "wbr.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "ntrneiel.mm"
include "elun.mm"
include "orbi12d.mm"
include "bibi12d.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "ralcom.mm"
include "syl6bb.mm"

theorem ntrneix13
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
  assert |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( I ` ( s u. t ) ) = ( ( I ` s ) u. ( I ` t ) ) <-> A. x e. B A. s e. ~P B A. t e. ~P B ( ( s u. t ) e. ( N ` x ) <-> ( s e. ( N ` x ) \/ t e. ( N ` x ) ) ) ) )

  proof
    wph
    vs
    cv
    #
    vt
    cv
    #
    cun
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
    cun
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
    wo
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
    @23
    cI
    @8
    @8
    cmap
    co
    wcel
    #
    @8
    @8
    cI
    wf
    wph
    @33
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
    ntrneiiex
    ad2antrr
    cI
    @8
    @8
    elmapi
    syl
    #
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
    @0
    @1
    cB
    @23
    @0
    cB
    wph
    @19
    @22
    simplr
    #
    elpwid
    @23
    @1
    cB
    @20
    @22
    simpr
    #
    elpwid
    unssd
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
    @39
    @31
    wb
    @23
    @4
    @5
    cB
    @23
    @4
    cB
    @23
    @8
    @8
    @0
    cI
    @34
    @37
    ffvelrnd
    elpwid
    @23
    @5
    cB
    @23
    @8
    @8
    @1
    cI
    @34
    @38
    ffvelrnd
    elpwid
    unssd
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
    @41
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
    @40
    ntrnei.r
    ad3antrrr
    #
    @23
    @40
    simpr
    #
    @41
    @2
    cB
    cvv
    wph
    @35
    @19
    @22
    @40
    @36
    ad3antrrr
    @41
    @0
    @1
    cB
    @41
    @0
    cB
    wph
    @19
    @22
    @40
    simpllr
    #
    elpwid
    @41
    @1
    cB
    @20
    @22
    @40
    simplr
    #
    elpwid
    unssd
    sselpwd
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
    wo
    @41
    @15
    @10
    @4
    @5
    elun
    @41
    @46
    @13
    @47
    @14
    @41
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
    @42
    @43
    @44
    ntrneiel
    @41
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
    @42
    @43
    @45
    ntrneiel
    orbi12d
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
