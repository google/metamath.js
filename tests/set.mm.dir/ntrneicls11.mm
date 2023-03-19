include "c0.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wral.mm"
include "cdif.mm"
include "wss.mm"
include "cin.mm"
include "wb.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrneiiex.mm"
include "elmapi.mm"
include "syl.mm"
include "0elpw.mm"
include "a1i.mm"
include "ffvelrnd.mm"
include "elpwid.mm"
include "reldisj.mm"
include "bicomd.mm"
include "difid.mm"
include "sseq2i.mm"
include "ss0b.mm"
include "bitri.mm"
include "disjr.mm"
include "3bitr3g.mm"
include "wa.mm"
include "wbr.mm"
include "adantr.mm"
include "simpr.mm"
include "ntrneiel.mm"
include "notbid.mm"
include "ralbidva.mm"
include "bitrd.mm"

theorem ntrneicls11
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
  let vl: setvar l
  assume ntrnei.o: |- O = ( i e. _V , j e. _V |-> ( k e. ( ~P j ^m i ) |-> ( l e. j |-> { m e. i | l e. ( k ` m ) } ) ) )
  assume ntrnei.f: |- F = ( ~P B O B )
  assume ntrnei.r: |- ( ph -> I F N )

  disjoint B i
  disjoint B j
  disjoint B k
  disjoint B l
  disjoint B m
  disjoint B x
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i x
  disjoint j k
  disjoint j l
  disjoint j m
  disjoint j x
  disjoint k l
  disjoint k m
  disjoint k x
  disjoint l m
  disjoint l x
  disjoint m x
  disjoint I k
  disjoint I l
  disjoint I m
  disjoint I x
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint ph x
  assert |- ( ph -> ( ( I ` (/) ) = (/) <-> A. x e. B -. (/) e. ( N ` x ) ) )

  proof
    wph
    c0
    cI
    cfv
    #
    c0
    wceq
    #
    vx
    cv
    #
    @0
    wcel
    #
    wn
    #
    vx
    cB
    wral
    #
    c0
    @2
    cN
    cfv
    wcel
    #
    wn
    #
    vx
    cB
    wral
    wph
    @0
    cB
    cB
    cdif
    #
    wss
    #
    @0
    cB
    cin
    c0
    wceq
    #
    @1
    @5
    wph
    @10
    @9
    wph
    @0
    cB
    wss
    @10
    @9
    wb
    wph
    @0
    cB
    wph
    cB
    cpw
    #
    @11
    c0
    cI
    wph
    cI
    @11
    @11
    cmap
    co
    wcel
    @11
    @11
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
    @11
    @11
    elmapi
    syl
    c0
    @11
    wcel
    #
    wph
    cB
    0elpw
    #
    a1i
    ffvelrnd
    elpwid
    @0
    cB
    cB
    reldisj
    syl
    bicomd
    @9
    @0
    c0
    wss
    @1
    @8
    c0
    @0
    cB
    difid
    sseq2i
    @0
    ss0b
    bitri
    vx
    @0
    cB
    disjr
    3bitr3g
    wph
    @4
    @7
    vx
    cB
    wph
    @2
    cB
    wcel
    #
    wa
    #
    @3
    @6
    @15
    cB
    c0
    vi
    vj
    vk
    vm
    cF
    cI
    cN
    cO
    @2
    vl
    ntrnei.o
    ntrnei.f
    wph
    cI
    cN
    cF
    wbr
    @14
    ntrnei.r
    adantr
    wph
    @14
    simpr
    @12
    @15
    @13
    a1i
    ntrneiel
    notbid
    ralbidva
    bitrd
end
