include "cnmhm.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cnlm.mm"
include "cof.mm"
include "clmhm.mm"
include "cnghm.mm"
include "nmhmrcl1.mm"
include "nmhmrcl2.mm"
include "anim12i.mm"
include "nmhmlmhm.mm"
include "lmhmplusg.mm"
include "syl2an.mm"
include "cabl.mm"
include "clmod.mm"
include "nlmlmod.mm"
include "lmodabl.mm"
include "3syl.mm"
include "adantl.mm"
include "nmhmnghm.mm"
include "adantr.mm"
include "nghmplusg.mm"
include "syl3anc.mm"
include "jca.mm"
include "isnmhm.mm"
include "sylanbrc.mm"

theorem nmhmplusg
  let c.pl: class .+
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  assume nmhmplusg.p: |- .+ = ( +g ` T )


  assert |- ( ( F e. ( S NMHom T ) /\ G e. ( S NMHom T ) ) -> ( F oF .+ G ) e. ( S NMHom T ) )

  proof
    cF
    cS
    cT
    cnmhm
    co
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    cS
    cnlm
    wcel
    #
    cT
    cnlm
    wcel
    #
    wa
    cF
    cG
    c.pl
    cof
    co
    #
    cS
    cT
    clmhm
    co
    #
    wcel
    #
    @6
    cS
    cT
    cnghm
    co
    #
    wcel
    #
    wa
    @6
    @0
    wcel
    @1
    @4
    @2
    @5
    cS
    cT
    cF
    nmhmrcl1
    cS
    cT
    cG
    nmhmrcl2
    #
    anim12i
    @3
    @8
    @10
    @1
    cF
    @7
    wcel
    cG
    @7
    wcel
    @8
    @2
    cS
    cT
    cF
    nmhmlmhm
    cS
    cT
    cG
    nmhmlmhm
    c.pl
    cF
    cG
    cS
    cT
    nmhmplusg.p
    lmhmplusg
    syl2an
    @3
    cT
    cabl
    wcel
    #
    cF
    @9
    wcel
    #
    cG
    @9
    wcel
    #
    @10
    @2
    @12
    @1
    @2
    @5
    cT
    clmod
    wcel
    @12
    @11
    cT
    nlmlmod
    cT
    lmodabl
    3syl
    adantl
    @1
    @13
    @2
    cS
    cT
    cF
    nmhmnghm
    adantr
    @2
    @14
    @1
    cS
    cT
    cG
    nmhmnghm
    adantl
    c.pl
    cS
    cT
    cF
    cG
    nmhmplusg.p
    nghmplusg
    syl3anc
    jca
    cS
    cT
    @6
    isnmhm
    sylanbrc
end
