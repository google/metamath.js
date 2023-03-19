include "clmod.mm"
include "wcel.mm"
include "cnzr.mm"
include "wa.mm"
include "clindf.mm"
include "wbr.mm"
include "cdm.mm"
include "w3a.mm"
include "cur.mm"
include "cfv.mm"
include "cvsca.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1l.mm"
include "wf.mm"
include "simp2.mm"
include "eqid.mm"
include "lindff.mm"
include "syl2anc.mm"
include "simp3.mm"
include "ffvelrnd.mm"
include "lmodvs1.mm"
include "c0g.mm"
include "wne.mm"
include "wn.mm"
include "crg.mm"
include "nzrring.mm"
include "ringidcl.mm"
include "syl.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "nzrnz.mm"
include "lindfind.mm"
include "syl22anc.mm"
include "eqneltrrd.mm"

theorem lindfind2
  let cE: class E
  let cF: class F
  let cK: class K
  let cL: class L
  let cW: class W
  assume lindfind2.k: |- K = ( LSpan ` W )
  assume lindfind2.l: |- L = ( Scalar ` W )


  assert |- ( ( ( W e. LMod /\ L e. NzRing ) /\ F LIndF W /\ E e. dom F ) -> -. ( F ` E ) e. ( K ` ( F " ( dom F \ { E } ) ) ) )

  proof
    cW
    clmod
    wcel
    #
    cL
    cnzr
    wcel
    #
    wa
    #
    cF
    cW
    clindf
    wbr
    #
    cE
    cF
    cdm
    #
    wcel
    #
    w3a
    #
    cL
    cur
    cfv
    #
    cE
    cF
    cfv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    @8
    cF
    @4
    cE
    csn
    cdif
    cima
    cK
    cfv
    #
    @6
    @0
    @8
    cW
    cbs
    cfv
    #
    wcel
    @10
    @8
    wceq
    @0
    @1
    @3
    @5
    simp1l
    #
    @6
    @4
    @12
    cE
    cF
    @6
    @3
    @0
    @4
    @12
    cF
    wf
    @2
    @3
    @5
    simp2
    #
    @13
    @12
    cF
    cW
    clmod
    @12
    eqid
    #
    lindff
    syl2anc
    @2
    @3
    @5
    simp3
    #
    ffvelrnd
    @9
    @7
    cL
    @12
    cW
    @8
    @15
    lindfind2.l
    @9
    eqid
    #
    @7
    eqid
    #
    lmodvs1
    syl2anc
    @6
    @3
    @5
    @7
    cL
    cbs
    cfv
    #
    wcel
    #
    @7
    cL
    c0g
    cfv
    #
    wne
    #
    @10
    @11
    wcel
    wn
    @14
    @16
    @2
    @3
    @20
    @5
    @1
    @20
    @0
    @1
    cL
    crg
    wcel
    @20
    cL
    nzrring
    @19
    cL
    @7
    @19
    eqid
    #
    @18
    ringidcl
    syl
    adantl
    3ad2ant1
    @2
    @3
    @22
    @5
    @1
    @22
    @0
    cL
    @7
    @21
    @18
    @21
    eqid
    #
    nzrnz
    adantl
    3ad2ant1
    @7
    @9
    cE
    cF
    @19
    cL
    cK
    cW
    @21
    @17
    lindfind2.k
    lindfind2.l
    @24
    @23
    lindfind
    syl22anc
    eqneltrrd
end
