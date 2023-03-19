include "cv.mm"
include "cun.mm"
include "cfv.mm"
include "wss.mm"
include "cpw.mm"
include "wral.mm"
include "wcel.mm"
include "wo.mm"
include "wi.mm"
include "wa.mm"
include "dfss3.mm"
include "wb.mm"
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
include "wbr.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "ntrneiel.mm"
include "elun.mm"
include "orbi12d.mm"
include "syl5bb.mm"
include "imbi12d.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "ralcom.mm"
include "syl6bb.mm"

theorem ntrneix3
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
  assert |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( I ` ( s u. t ) ) C_ ( ( I ` s ) u. ( I ` t ) ) <-> A. x e. B A. s e. ~P B A. t e. ~P B ( ( s u. t ) e. ( N ` x ) -> ( s e. ( N ` x ) \/ t e. ( N ` x ) ) ) ) )

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
    wss
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
    wi
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
    @7
    @10
    @6
    wcel
    #
    vx
    @3
    wral
    #
    @20
    @1
    @8
    wcel
    #
    wa
    #
    @21
    vx
    @3
    @6
    dfss3
    @25
    @23
    @10
    @3
    wcel
    #
    @22
    wi
    #
    vx
    cB
    wral
    #
    @21
    @25
    @3
    cB
    wss
    @23
    @28
    wb
    @25
    @3
    cB
    @25
    @8
    @8
    @2
    cI
    @25
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
    @29
    @19
    @24
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
    @25
    @2
    cB
    cvv
    wph
    cB
    cvv
    wcel
    #
    @19
    @24
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
    @25
    @0
    @1
    cB
    @25
    @0
    cB
    wph
    @19
    @24
    simplr
    elpwid
    @25
    @1
    cB
    @20
    @24
    simpr
    elpwid
    unssd
    sselpwd
    ffvelrnd
    elpwid
    @22
    vx
    @3
    cB
    ralss
    syl
    @25
    @27
    @16
    vx
    cB
    @25
    @10
    cB
    wcel
    #
    wa
    #
    @26
    @12
    @22
    @15
    @33
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
    @24
    @32
    ntrnei.r
    ad3antrrr
    #
    @25
    @32
    simpr
    #
    @33
    @2
    cB
    cvv
    wph
    @30
    @19
    @24
    @32
    @31
    ad3antrrr
    @33
    @0
    @1
    cB
    @33
    @0
    cB
    wph
    @19
    @24
    @32
    simpllr
    #
    elpwid
    @33
    @1
    cB
    @20
    @24
    @32
    simplr
    #
    elpwid
    unssd
    sselpwd
    ntrneiel
    @22
    @10
    @4
    wcel
    #
    @10
    @5
    wcel
    #
    wo
    @33
    @15
    @10
    @4
    @5
    elun
    @33
    @38
    @13
    @39
    @14
    @33
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
    @34
    @35
    @36
    ntrneiel
    @33
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
    @34
    @35
    @37
    ntrneiel
    orbi12d
    syl5bb
    imbi12d
    ralbidva
    bitrd
    syl5bb
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
