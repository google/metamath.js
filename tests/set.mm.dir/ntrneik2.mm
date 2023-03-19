include "cv.mm"
include "cfv.mm"
include "wss.mm"
include "cpw.mm"
include "wral.mm"
include "wcel.mm"
include "wel.mm"
include "wi.mm"
include "wa.mm"
include "wal.mm"
include "wb.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "ntrneiiex.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "elpwid.mm"
include "sselda.mm"
include "biimt.mm"
include "pm5.74da.mm"
include "bi2.04.mm"
include "syl6bb.mm"
include "albidv.mm"
include "dfss2.mm"
include "df-ral.mm"
include "3bitr4g.mm"
include "wbr.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "simplr.mm"
include "ntrneiel.mm"
include "imbi1d.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "ralcom.mm"

theorem ntrneik2
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
  assert |- ( ph -> ( A. s e. ~P B ( I ` s ) C_ s <-> A. x e. B A. s e. ~P B ( s e. ( N ` x ) -> x e. s ) ) )

  proof
    wph
    vs
    cv
    #
    cI
    cfv
    #
    @0
    wss
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
    wcel
    #
    vx
    vs
    wel
    #
    wi
    #
    vx
    cB
    wral
    #
    vs
    @3
    wral
    @7
    vs
    @3
    wral
    vx
    cB
    wral
    wph
    @2
    @8
    vs
    @3
    wph
    @0
    @3
    wcel
    #
    wa
    #
    @2
    @4
    @1
    wcel
    #
    @6
    wi
    #
    vx
    cB
    wral
    #
    @8
    @10
    @12
    vx
    wal
    @4
    cB
    wcel
    #
    @12
    wi
    #
    vx
    wal
    @2
    @13
    @10
    @12
    @15
    vx
    @10
    @12
    @11
    @14
    @6
    wi
    #
    wi
    @15
    @10
    @11
    @6
    @16
    @10
    @11
    wa
    @14
    @6
    @16
    wb
    @10
    @1
    cB
    @4
    @10
    @1
    cB
    wph
    @3
    @3
    @0
    cI
    wph
    cI
    @3
    @3
    cmap
    co
    wcel
    @3
    @3
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
    @3
    @3
    elmapi
    syl
    ffvelrnda
    elpwid
    sselda
    @14
    @6
    biimt
    syl
    pm5.74da
    @11
    @14
    @6
    bi2.04
    syl6bb
    albidv
    vx
    @1
    @0
    dfss2
    @12
    vx
    cB
    df-ral
    3bitr4g
    @10
    @12
    @7
    vx
    cB
    @10
    @14
    wa
    #
    @11
    @5
    @6
    @17
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
    @4
    vl
    ntrnei.o
    ntrnei.f
    wph
    cI
    cN
    cF
    wbr
    @9
    @14
    ntrnei.r
    ad2antrr
    @10
    @14
    simpr
    wph
    @9
    @14
    simplr
    ntrneiel
    imbi1d
    ralbidva
    bitrd
    ralbidva
    @7
    vs
    vx
    @3
    cB
    ralcom
    syl6bb
end
