include "cv.mm"
include "cun.mm"
include "wceq.mm"
include "cfv.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "wcel.mm"
include "wo.mm"
include "wa.mm"
include "wss.mm"
include "wb.mm"
include "eqss.mm"
include "a1i.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrneiiex.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "elpwid.mm"
include "adantr.mm"
include "adantlr.mm"
include "unssd.mm"
include "biantrurd.mm"
include "dfss3.mm"
include "elun.mm"
include "ralbii.mm"
include "bitri.mm"
include "3bitr2d.mm"
include "imbi2d.mm"
include "r19.21v.mm"
include "wbr.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "simpllr.mm"
include "ntrneiel.mm"
include "simplr.mm"
include "orbi12d.mm"
include "ralbidva.mm"
include "w3a.mm"
include "wal.mm"
include "alrot3.mm"
include "3anrot.mm"
include "imbi1i.mm"
include "albii.mm"
include "2albii.mm"
include "bitr2i.mm"
include "r3al.mm"
include "3bitr4i.mm"
include "syl6bb.mm"

theorem ntrneixb
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
  assert |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( ( s u. t ) = B -> ( ( I ` s ) u. ( I ` t ) ) = B ) <-> A. x e. B A. s e. ~P B A. t e. ~P B ( ( s u. t ) = B -> ( s e. ( N ` x ) \/ t e. ( N ` x ) ) ) ) )

  proof
    wph
    vs
    cv
    #
    vt
    cv
    #
    cun
    cB
    wceq
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
    cB
    wceq
    #
    wi
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
    @11
    wcel
    #
    wo
    #
    wi
    #
    vx
    cB
    wral
    #
    vt
    @8
    wral
    #
    vs
    @8
    wral
    #
    @15
    vt
    @8
    wral
    vs
    @8
    wral
    vx
    cB
    wral
    #
    wph
    @9
    @17
    vs
    @8
    wph
    @0
    @8
    wcel
    #
    wa
    #
    @7
    @16
    vt
    @8
    @21
    @1
    @8
    wcel
    #
    wa
    #
    @7
    @2
    @10
    @3
    wcel
    #
    @10
    @4
    wcel
    #
    wo
    #
    vx
    cB
    wral
    #
    wi
    #
    @2
    @26
    wi
    #
    vx
    cB
    wral
    #
    @16
    @23
    @6
    @27
    @2
    @23
    @6
    @5
    cB
    wss
    #
    cB
    @5
    wss
    #
    wa
    #
    @32
    @27
    @6
    @33
    wb
    @23
    @5
    cB
    eqss
    a1i
    @23
    @31
    @32
    @23
    @3
    @4
    cB
    @21
    @3
    cB
    wss
    @22
    @21
    @3
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
    #
    ffvelrnda
    elpwid
    adantr
    wph
    @22
    @4
    cB
    wss
    @20
    wph
    @22
    wa
    @4
    cB
    wph
    @8
    @8
    @1
    cI
    @34
    ffvelrnda
    elpwid
    adantlr
    unssd
    biantrurd
    @32
    @27
    wb
    @23
    @32
    @10
    @5
    wcel
    #
    vx
    cB
    wral
    @27
    vx
    cB
    @5
    dfss3
    @35
    @26
    vx
    cB
    @10
    @3
    @4
    elun
    ralbii
    bitri
    a1i
    3bitr2d
    imbi2d
    @30
    @28
    wb
    @23
    @2
    @26
    vx
    cB
    r19.21v
    a1i
    @23
    @29
    @15
    vx
    cB
    @23
    @10
    cB
    wcel
    #
    wa
    #
    @26
    @14
    @2
    @37
    @24
    @12
    @25
    @13
    @37
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
    @20
    @22
    @36
    ntrnei.r
    ad3antrrr
    #
    @23
    @36
    simpr
    #
    wph
    @20
    @22
    @36
    simpllr
    ntrneiel
    @37
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
    @38
    @39
    @21
    @22
    @36
    simplr
    ntrneiel
    orbi12d
    imbi2d
    ralbidva
    3bitr2d
    ralbidva
    ralbidva
    @20
    @22
    @36
    w3a
    #
    @15
    wi
    #
    vx
    wal
    #
    vt
    wal
    vs
    wal
    #
    @36
    @20
    @22
    w3a
    #
    @15
    wi
    #
    vt
    wal
    vs
    wal
    vx
    wal
    #
    @18
    @19
    @46
    @45
    vx
    wal
    #
    vt
    wal
    vs
    wal
    @43
    @45
    vx
    vs
    vt
    alrot3
    @47
    @42
    vs
    vt
    @45
    @41
    vx
    @44
    @40
    @15
    @36
    @20
    @22
    3anrot
    imbi1i
    albii
    2albii
    bitr2i
    @15
    vs
    vt
    vx
    @8
    @8
    cB
    r3al
    @15
    vx
    vs
    vt
    cB
    @8
    @8
    r3al
    3bitr4i
    syl6bb
end
