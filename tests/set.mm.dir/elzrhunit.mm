include "cdr.mm"
include "wcel.mm"
include "cchr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cz.mm"
include "wne.mm"
include "wfn.mm"
include "ccnv.mm"
include "cui.mm"
include "cima.mm"
include "crg.mm"
include "simpll.mm"
include "drngring.mm"
include "zring.mm"
include "crh.mm"
include "co.mm"
include "wf.mm"
include "zrhrhm.mm"
include "zringbas.mm"
include "rhmf.mm"
include "ffn.mm"
include "3syl.mm"
include "csn.mm"
include "cdif.mm"
include "simprl.mm"
include "wn.mm"
include "elsng.mm"
include "necon3bbid.mm"
include "biimpar.mm"
include "adantl.mm"
include "eldifd.mm"
include "zrhunitpreima.mm"
include "adantr.mm"
include "eleqtrrd.mm"
include "elpreima.mm"
include "simplbda.mm"
include "syl2anc.mm"

theorem elzrhunit
  let cB: class B
  let cR: class R
  let cL: class L
  let cM: class M
  let c.0: class .0.
  let vx: setvar x
  assume zrhker.0: |- B = ( Base ` R )
  assume zrhker.1: |- L = ( ZRHom ` R )
  assume zrhker.2: |- .0. = ( 0g ` R )


  assert |- ( ( ( R e. DivRing /\ ( chr ` R ) = 0 ) /\ ( M e. ZZ /\ M =/= 0 ) ) -> ( L ` M ) e. ( Unit ` R ) )

  proof
    cR
    cdr
    wcel
    #
    cR
    cchr
    cfv
    cc0
    wceq
    #
    wa
    #
    cM
    cz
    wcel
    #
    cM
    cc0
    wne
    #
    wa
    #
    wa
    #
    cL
    cz
    wfn
    #
    cM
    cL
    ccnv
    cR
    cui
    cfv
    #
    cima
    #
    wcel
    #
    cM
    cL
    cfv
    @8
    wcel
    #
    @6
    @0
    cR
    crg
    wcel
    #
    @7
    @0
    @1
    @5
    simpll
    cR
    drngring
    @12
    cL
    zring
    cR
    crh
    co
    wcel
    cz
    cB
    cL
    wf
    @7
    cR
    cL
    zrhker.1
    zrhrhm
    cz
    cB
    zring
    cR
    cL
    zringbas
    zrhker.0
    rhmf
    cz
    cB
    cL
    ffn
    3syl
    3syl
    @6
    cM
    cz
    cc0
    csn
    #
    cdif
    #
    @9
    @6
    cM
    cz
    @13
    @2
    @3
    @4
    simprl
    @5
    cM
    @13
    wcel
    #
    wn
    #
    @2
    @3
    @16
    @4
    @3
    @15
    cM
    cc0
    cM
    cc0
    cz
    elsng
    necon3bbid
    biimpar
    adantl
    eldifd
    @2
    @9
    @14
    wceq
    @5
    cB
    cR
    cL
    c.0
    zrhker.0
    zrhker.1
    zrhker.2
    zrhunitpreima
    adantr
    eleqtrrd
    @7
    @10
    @3
    @11
    cz
    cM
    @8
    cL
    elpreima
    simplbda
    syl2anc
end
