include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cfv.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "wal.mm"
include "wn.mm"
include "con34b.mm"
include "albii.mm"
include "19.21v.mm"
include "nne.mm"
include "wss.mm"
include "elin.mm"
include "imbi1i.mm"
include "wb.mm"
include "noel.mm"
include "imnot.mm"
include "ax-mp.mm"
include "bitr2i.mm"
include "dfss2.mm"
include "ss0b.mm"
include "3bitr2i.mm"
include "imbi12i.mm"
include "3bitrri.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrneiiex.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "elpwid.mm"
include "sseld.mm"
include "adantrd.mm"
include "imp.mm"
include "biimt.mm"
include "pm5.74da.mm"
include "bi2.04.mm"
include "syl6bb.mm"
include "albidv.mm"
include "df-ral.mm"
include "syl6bbr.mm"
include "wbr.mm"
include "ad3antrrr.mm"
include "simpr.mm"
include "simpllr.mm"
include "ntrneiel.mm"
include "simplr.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "w3a.mm"
include "alrot3.mm"
include "3anrot.mm"
include "2albii.mm"
include "r3al.mm"
include "3bitr4i.mm"

theorem ntrneikb
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
  assert |- ( ph -> ( A. s e. ~P B A. t e. ~P B ( ( s i^i t ) = (/) -> ( ( I ` s ) i^i ( I ` t ) ) = (/) ) <-> A. x e. B A. s e. ~P B A. t e. ~P B ( ( s e. ( N ` x ) /\ t e. ( N ` x ) ) -> ( s i^i t ) =/= (/) ) ) )

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
    c0
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
    cin
    #
    c0
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
    @9
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
    @12
    wcel
    #
    wa
    #
    @2
    c0
    wne
    #
    wi
    #
    vx
    cB
    wral
    #
    vt
    @9
    wral
    #
    vs
    @9
    wral
    #
    @17
    vt
    @9
    wral
    vs
    @9
    wral
    vx
    cB
    wral
    #
    wph
    @10
    @19
    vs
    @9
    wph
    @0
    @9
    wcel
    #
    wa
    #
    @8
    @18
    vt
    @9
    @8
    @11
    @4
    wcel
    #
    @11
    @5
    wcel
    #
    wa
    #
    @16
    wi
    #
    vx
    wal
    #
    @23
    @1
    @9
    wcel
    #
    wa
    #
    @18
    @28
    @16
    wn
    #
    @26
    wn
    #
    wi
    #
    vx
    wal
    @31
    @32
    vx
    wal
    #
    wi
    @8
    @27
    @33
    vx
    @26
    @16
    con34b
    albii
    @31
    @32
    vx
    19.21v
    @31
    @3
    @34
    @7
    @2
    c0
    nne
    @34
    @11
    @6
    wcel
    #
    @11
    c0
    wcel
    #
    wi
    #
    vx
    wal
    @6
    c0
    wss
    @7
    @32
    @37
    vx
    @37
    @26
    @36
    wi
    #
    @32
    @35
    @26
    @36
    @11
    @4
    @5
    elin
    imbi1i
    @36
    wn
    @38
    @32
    wb
    @11
    noel
    @26
    @36
    imnot
    ax-mp
    bitr2i
    albii
    vx
    @6
    c0
    dfss2
    @6
    ss0b
    3bitr2i
    imbi12i
    3bitrri
    @30
    @28
    @27
    vx
    cB
    wral
    #
    @18
    @30
    @28
    @11
    cB
    wcel
    #
    @27
    wi
    #
    vx
    wal
    @39
    @30
    @27
    @41
    vx
    @30
    @27
    @26
    @40
    @16
    wi
    #
    wi
    @41
    @30
    @26
    @16
    @42
    @30
    @26
    wa
    @40
    @16
    @42
    wb
    @30
    @26
    @40
    @30
    @24
    @40
    @25
    @30
    @4
    cB
    @11
    @30
    @4
    cB
    @23
    @4
    @9
    wcel
    @29
    wph
    @9
    @9
    @0
    cI
    wph
    cI
    @9
    @9
    cmap
    co
    wcel
    @9
    @9
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
    @9
    @9
    elmapi
    syl
    ffvelrnda
    adantr
    elpwid
    sseld
    adantrd
    imp
    @40
    @16
    biimt
    syl
    pm5.74da
    @26
    @40
    @16
    bi2.04
    syl6bb
    albidv
    @27
    vx
    cB
    df-ral
    syl6bbr
    @30
    @27
    @17
    vx
    cB
    @30
    @40
    wa
    #
    @26
    @15
    @16
    @43
    @24
    @13
    @25
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
    @11
    vl
    ntrnei.o
    ntrnei.f
    wph
    cI
    cN
    cF
    wbr
    @22
    @29
    @40
    ntrnei.r
    ad3antrrr
    #
    @30
    @40
    simpr
    #
    wph
    @22
    @29
    @40
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
    @11
    vl
    ntrnei.o
    ntrnei.f
    @44
    @45
    @23
    @29
    @40
    simplr
    ntrneiel
    anbi12d
    imbi1d
    ralbidva
    bitrd
    syl5bb
    ralbidva
    ralbidva
    @22
    @29
    @40
    w3a
    #
    @17
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
    @40
    @22
    @29
    w3a
    #
    @17
    wi
    #
    vt
    wal
    vs
    wal
    vx
    wal
    #
    @20
    @21
    @52
    @51
    vx
    wal
    #
    vt
    wal
    vs
    wal
    @49
    @51
    vx
    vs
    vt
    alrot3
    @53
    @48
    vs
    vt
    @51
    @47
    vx
    @50
    @46
    @17
    @40
    @22
    @29
    3anrot
    imbi1i
    albii
    2albii
    bitr2i
    @17
    vs
    vt
    vx
    @9
    @9
    cB
    r3al
    @17
    vx
    vs
    vt
    cB
    @9
    @9
    r3al
    3bitr4i
    syl6bb
end
