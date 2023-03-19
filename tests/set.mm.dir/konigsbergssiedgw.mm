include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "cconcat.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "cpw.mm"
include "crab.mm"
include "cc0.mm"
include "cfzo.mm"
include "wf.mm"
include "cle.mm"
include "wbr.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "konigsbergssiedgwpr.mm"
include "wrdf.mm"
include "wss.mm"
include "prprrab.mm"
include "wi.mm"
include "2re.mm"
include "eqlei2.mm"
include "a1i.mm"
include "ss2rabi.mm"
include "eqsstr3i.mm"
include "fss.mm"
include "mpan2.mm"
include "iswrdb.mm"
include "sylibr.mm"
include "3syl.mm"

theorem konigsbergssiedgw
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cE: class E
  let cG: class G
  let cV: class V
  assume konigsberg.v: |- V = ( 0 ... 3 )
  assume konigsberg.e: |- E = <" { 0 , 1 } { 0 , 2 } { 0 , 3 } { 1 , 2 } { 1 , 2 } { 2 , 3 } { 2 , 3 } ">
  assume konigsberg.g: |- G = <. V , E >.

  disjoint V x
  assert |- ( ( A e. Word _V /\ B e. Word _V /\ E = ( A ++ B ) ) -> A e. Word { x e. ( ~P V \ { (/) } ) | ( # ` x ) <_ 2 } )

  proof
    cA
    cvv
    cword
    #
    wcel
    cB
    @0
    wcel
    cE
    cA
    cB
    cconcat
    co
    wceq
    w3a
    cA
    vx
    cv
    #
    chash
    cfv
    #
    c2
    wceq
    #
    vx
    cV
    cpw
    #
    crab
    #
    cword
    wcel
    cc0
    cA
    chash
    cfv
    cfzo
    co
    #
    @5
    cA
    wf
    #
    cA
    @2
    c2
    cle
    wbr
    #
    vx
    @4
    c0
    csn
    cdif
    #
    crab
    #
    cword
    wcel
    #
    vx
    cA
    cB
    cE
    cG
    cV
    konigsberg.v
    konigsberg.e
    konigsberg.g
    konigsbergssiedgwpr
    @5
    cA
    wrdf
    @7
    @6
    @10
    cA
    wf
    #
    @11
    @7
    @5
    @10
    wss
    @12
    @5
    @3
    vx
    @9
    crab
    @10
    vx
    cV
    prprrab
    @3
    @8
    vx
    @9
    @3
    @8
    wi
    @1
    @9
    wcel
    c2
    @2
    2re
    eqlei2
    a1i
    ss2rabi
    eqsstr3i
    @6
    @5
    @10
    cA
    fss
    mpan2
    @10
    cA
    iswrdb
    sylibr
    3syl
end
