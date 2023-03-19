include "cv.mm"
include "wss.mm"
include "cfv.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wal.mm"
include "dfss2.mm"
include "imbi2i.mm"
include "19.21v.mm"
include "bitr4i.mm"
include "ax-1.mm"
include "wn.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "simpll.mm"
include "ntrneiiex.mm"
include "elmapi.mm"
include "3syl.mm"
include "simplr.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "sselda.mm"
include "pm2.24d.mm"
include "ex.mm"
include "com23.mm"
include "a1dd.mm"
include "idd.mm"
include "jad.mm"
include "impbid2.mm"
include "albidv.mm"
include "df-ral.mm"
include "syl6bbr.mm"
include "wbr.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "simpllr.mm"
include "ntrneiel.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "impexp.mm"
include "ancomst.mm"
include "bitr3i.mm"
include "syl6bb.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "ralcom.mm"

theorem ntrneiiso
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
  assert |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( s C_ t -> ( I ` s ) C_ ( I ` t ) ) <-> A. x e. B A. s e. ~P B A. t e. ~P B ( ( s e. ( N ` x ) /\ s C_ t ) -> t e. ( N ` x ) ) ) )

  proof
    wph
    vs
    cv
    #
    vt
    cv
    #
    wss
    #
    @0
    cI
    cfv
    #
    @1
    cI
    cfv
    #
    wss
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
    @7
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
    wa
    @1
    @10
    wcel
    #
    wi
    #
    vt
    @7
    wral
    #
    vx
    cB
    wral
    #
    vs
    @7
    wral
    @14
    vs
    @7
    wral
    vx
    cB
    wral
    wph
    @8
    @15
    vs
    @7
    wph
    @0
    @7
    wcel
    #
    wa
    #
    @8
    @13
    vx
    cB
    wral
    #
    vt
    @7
    wral
    @15
    @17
    @6
    @18
    vt
    @7
    @6
    @2
    @9
    @3
    wcel
    #
    @9
    @4
    wcel
    #
    wi
    #
    wi
    #
    vx
    wal
    #
    @17
    @1
    @7
    wcel
    #
    wa
    #
    @18
    @6
    @2
    @21
    vx
    wal
    #
    wi
    @23
    @5
    @26
    @2
    vx
    @3
    @4
    dfss2
    imbi2i
    @2
    @21
    vx
    19.21v
    bitr4i
    @25
    @23
    @22
    vx
    cB
    wral
    #
    @18
    @25
    @23
    @9
    cB
    wcel
    #
    @22
    wi
    #
    vx
    wal
    @27
    @25
    @22
    @29
    vx
    @25
    @22
    @29
    @22
    @28
    ax-1
    @25
    @28
    @22
    @22
    @25
    @28
    wn
    #
    @21
    @2
    @25
    @19
    @30
    @20
    @25
    @19
    @30
    @20
    wi
    @25
    @19
    wa
    @28
    @20
    @25
    @3
    cB
    @9
    @25
    @3
    cB
    @25
    @7
    @7
    @0
    cI
    @25
    wph
    cI
    @7
    @7
    cmap
    co
    wcel
    @7
    @7
    cI
    wf
    wph
    @16
    @24
    simpll
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
    @7
    @7
    elmapi
    3syl
    wph
    @16
    @24
    simplr
    ffvelrnd
    elpwid
    sselda
    pm2.24d
    ex
    com23
    a1dd
    @25
    @22
    idd
    jad
    impbid2
    albidv
    @22
    vx
    cB
    df-ral
    syl6bbr
    @25
    @22
    @13
    vx
    cB
    @25
    @28
    wa
    #
    @22
    @2
    @11
    @12
    wi
    #
    wi
    #
    @13
    @31
    @21
    @32
    @2
    @31
    @19
    @11
    @20
    @12
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
    @9
    vl
    ntrnei.o
    ntrnei.f
    wph
    cI
    cN
    cF
    wbr
    @16
    @24
    @28
    ntrnei.r
    ad3antrrr
    #
    @25
    @28
    simpr
    #
    wph
    @16
    @24
    @28
    simpllr
    ntrneiel
    @31
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
    @9
    vl
    ntrnei.o
    ntrnei.f
    @34
    @35
    @17
    @24
    @28
    simplr
    ntrneiel
    imbi12d
    imbi2d
    @33
    @2
    @11
    wa
    @12
    wi
    @13
    @2
    @11
    @12
    impexp
    @2
    @11
    @12
    ancomst
    bitr3i
    syl6bb
    ralbidva
    bitrd
    syl5bb
    ralbidva
    @13
    vt
    vx
    @7
    cB
    ralcom
    syl6bb
    ralbidva
    @14
    vs
    vx
    @7
    cB
    ralcom
    syl6bb
end
