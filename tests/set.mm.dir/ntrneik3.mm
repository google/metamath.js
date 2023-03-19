include "cv.mm"
include "cfv.mm"
include "cin.mm"
include "wss.mm"
include "cpw.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wi.mm"
include "dfss3.mm"
include "wb.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrneiiex.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "elpwid.mm"
include "ssinss1.mm"
include "adantr.mm"
include "ralss.mm"
include "elin.mm"
include "wbr.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "simpllr.mm"
include "ntrneiel.mm"
include "simplr.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "cvv.mm"
include "ntrneibex.mm"
include "sselpwd.mm"
include "imbi12d.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "ralcom.mm"
include "syl6bb.mm"

theorem ntrneik3
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
  assert |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( ( I ` s ) i^i ( I ` t ) ) C_ ( I ` ( s i^i t ) ) <-> A. x e. B A. s e. ~P B A. t e. ~P B ( ( s e. ( N ` x ) /\ t e. ( N ` x ) ) -> ( s i^i t ) e. ( N ` x ) ) ) )

  proof
    wph
    vs
    cv
    #
    cI
    cfv
    #
    vt
    cv
    #
    cI
    cfv
    #
    cin
    #
    @0
    @2
    cin
    #
    cI
    cfv
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
    @0
    vx
    cv
    #
    cN
    cfv
    #
    wcel
    #
    @2
    @11
    wcel
    #
    wa
    #
    @5
    @11
    wcel
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
    @4
    wral
    #
    @20
    @2
    @8
    wcel
    #
    wa
    #
    @21
    vx
    @4
    @6
    dfss3
    @25
    @23
    @10
    @4
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
    @4
    cB
    wss
    #
    @23
    @28
    wb
    @20
    @29
    @24
    @20
    @1
    cB
    wss
    @29
    @20
    @1
    cB
    wph
    @8
    @8
    @0
    cI
    wph
    cI
    @8
    @8
    cmap
    co
    wcel
    @8
    @8
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
    @8
    @8
    elmapi
    syl
    ffvelrnda
    elpwid
    @1
    @3
    cB
    ssinss1
    syl
    adantr
    @22
    vx
    @4
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
    @14
    @22
    @15
    @26
    @10
    @1
    wcel
    #
    @10
    @3
    wcel
    #
    wa
    @31
    @14
    @10
    @1
    @3
    elin
    @31
    @32
    @12
    @33
    @13
    @31
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
    wph
    cI
    cN
    cF
    wbr
    @19
    @24
    @30
    ntrnei.r
    ad3antrrr
    #
    @25
    @30
    simpr
    #
    wph
    @19
    @24
    @30
    simpllr
    #
    ntrneiel
    @31
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
    @34
    @35
    @20
    @24
    @30
    simplr
    ntrneiel
    anbi12d
    syl5bb
    @31
    cB
    @5
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
    @31
    @5
    cB
    cvv
    wph
    cB
    cvv
    wcel
    @19
    @24
    @30
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
    ad3antrrr
    @31
    @0
    cB
    wss
    @5
    cB
    wss
    @31
    @0
    cB
    @36
    elpwid
    @0
    @2
    cB
    ssinss1
    syl
    sselpwd
    ntrneiel
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
