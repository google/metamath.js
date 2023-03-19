include "cv.mm"
include "cfv.mm"
include "wss.mm"
include "cpw.mm"
include "wral.mm"
include "wel.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "wb.mm"
include "simpr.mm"
include "wal.mm"
include "elpwi.mm"
include "sselda.mm"
include "biimt.mm"
include "syl.mm"
include "pm5.74da.mm"
include "bi2.04.mm"
include "syl6bb.mm"
include "albidv.mm"
include "dfss2.mm"
include "df-ral.mm"
include "3bitr4g.mm"
include "wbr.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "ntrneiel.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "ralcom.mm"

theorem ntrneix2
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
  assert |- ( ph -> ( A. s e. ~P B s C_ ( I ` s ) <-> A. x e. B A. s e. ~P B ( x e. s -> s e. ( N ` x ) ) ) )

  proof
    wph
    vs
    cv
    #
    @0
    cI
    cfv
    #
    wss
    #
    vs
    cB
    cpw
    #
    wral
    vx
    vs
    wel
    #
    @0
    vx
    cv
    #
    cN
    cfv
    wcel
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
    @5
    @1
    wcel
    #
    wi
    #
    vx
    cB
    wral
    #
    @8
    @10
    @9
    @2
    @13
    wb
    wph
    @9
    simpr
    @9
    @12
    vx
    wal
    @5
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
    @9
    @12
    @15
    vx
    @9
    @12
    @4
    @14
    @11
    wi
    #
    wi
    @15
    @9
    @4
    @11
    @16
    @9
    @4
    wa
    @14
    @11
    @16
    wb
    @9
    @0
    cB
    @5
    @0
    cB
    elpwi
    sselda
    @14
    @11
    biimt
    syl
    pm5.74da
    @4
    @14
    @11
    bi2.04
    syl6bb
    albidv
    vx
    @0
    @1
    dfss2
    @12
    vx
    cB
    df-ral
    3bitr4g
    syl
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
    @6
    @4
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
    @5
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
    imbi2d
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
