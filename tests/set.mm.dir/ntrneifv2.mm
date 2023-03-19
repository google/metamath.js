include "ccnv.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "wfun.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "wb.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf1o.mm"
include "ntrneif1o.mm"
include "ntrneinex.mm"
include "wfo.mm"
include "dff1o3.mm"
include "simprbi.mm"
include "adantr.mm"
include "crn.mm"
include "df-rn.mm"
include "f1ofo.mm"
include "forn.mm"
include "syl.mm"
include "syl5eqr.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "jca.mm"
include "syl2anc.mm"
include "funbrfvb.mm"
include "ntrneiiex.mm"
include "brcnvg.mm"
include "bitrd.mm"
include "mpbird.mm"

theorem ntrneifv2
  let wph: wff ph
  let cB: class B
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cI: class I
  let cN: class N
  let cO: class O
  let vl: setvar l
  assume ntrnei.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume ntrnei.f: |- F = ( ~P B O B )
  assume ntrnei.r: |- ( ph -> I F N )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B m
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint k l
  disjoint k m
  disjoint l m
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  assert |- ( ph -> ( `' F ` N ) = I )

  proof
    wph
    cN
    cF
    ccnv
    #
    cfv
    cI
    wceq
    #
    cI
    cN
    cF
    wbr
    #
    ntrnei.r
    wph
    @1
    cN
    cI
    @0
    wbr
    #
    @2
    wph
    @0
    wfun
    #
    cN
    @0
    cdm
    #
    wcel
    #
    wa
    #
    @1
    @3
    wb
    wph
    cB
    cpw
    #
    @8
    cmap
    co
    #
    @8
    cpw
    cB
    cmap
    co
    #
    cF
    wf1o
    #
    cN
    @10
    wcel
    #
    @7
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
    ntrneif1o
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
    #
    @11
    @12
    wa
    @4
    @6
    @11
    @4
    @12
    @11
    @9
    @10
    cF
    wfo
    #
    @4
    @9
    @10
    cF
    dff1o3
    simprbi
    adantr
    @11
    @6
    @12
    @11
    @5
    @10
    cN
    @11
    @5
    cF
    crn
    #
    @10
    cF
    df-rn
    @11
    @14
    @15
    @10
    wceq
    @9
    @10
    cF
    f1ofo
    @9
    @10
    cF
    forn
    syl
    syl5eqr
    eleq2d
    biimpar
    jca
    syl2anc
    cN
    cI
    @0
    funbrfvb
    syl
    wph
    @12
    cI
    @9
    wcel
    @3
    @2
    wb
    @13
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
    cN
    cI
    @10
    @9
    cF
    brcnvg
    syl2anc
    bitrd
    mpbird
end
