include "wcel.mm"
include "cs1.mm"
include "cgsu.mm"
include "co.mm"
include "cc0.mm"
include "cop.mm"
include "csn.mm"
include "cplusg.mm"
include "cfv.mm"
include "cseq.mm"
include "s1val.mm"
include "oveq2d.mm"
include "cbs.mm"
include "cdm.mm"
include "eqid.mm"
include "elfvdm.mm"
include "eleq2s.mm"
include "cuz.mm"
include "cn0.mm"
include "0nn0.mm"
include "nn0uz.mm"
include "eleqtri.mm"
include "a1i.mm"
include "wf.mm"
include "cfz.mm"
include "wf1o.mm"
include "cz.mm"
include "0z.mm"
include "f1osng.mm"
include "mpan.mm"
include "f1of.mm"
include "syl.mm"
include "snssi.mm"
include "fssd.mm"
include "wceq.mm"
include "fzsn.mm"
include "ax-mp.mm"
include "feq2i.mm"
include "sylibr.mm"
include "gsumval2.mm"
include "fvsng.mm"
include "seq1i.mm"
include "3eqtrd.mm"

theorem gsumws1
  let cB: class B
  let cS: class S
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  let cW: class W
  let cX: class X
  assume gsumwcl.b: |- B = ( Base ` G )


  assert |- ( S e. B -> ( G gsum <" S "> ) = S )

  proof
    cS
    cB
    wcel
    #
    cG
    cS
    cs1
    #
    cgsu
    co
    cG
    cc0
    cS
    cop
    csn
    #
    cgsu
    co
    cc0
    cG
    cplusg
    cfv
    #
    @2
    cc0
    cseq
    cfv
    cS
    @0
    @1
    @2
    cG
    cgsu
    cS
    cB
    s1val
    oveq2d
    @0
    cB
    @3
    @2
    cG
    cc0
    cc0
    cbs
    cdm
    #
    gsumwcl.b
    @3
    eqid
    cG
    @4
    wcel
    cS
    cG
    cbs
    cfv
    cB
    cS
    cG
    cbs
    elfvdm
    gsumwcl.b
    eleq2s
    cc0
    cc0
    cuz
    cfv
    #
    wcel
    @0
    cc0
    cn0
    @5
    0nn0
    nn0uz
    eleqtri
    a1i
    @0
    cc0
    csn
    #
    cB
    @2
    wf
    cc0
    cc0
    cfz
    co
    #
    cB
    @2
    wf
    @0
    @6
    cS
    csn
    #
    cB
    @2
    @0
    @6
    @8
    @2
    wf1o
    #
    @6
    @8
    @2
    wf
    cc0
    cz
    wcel
    #
    @0
    @9
    0z
    cc0
    cS
    cz
    cB
    f1osng
    mpan
    @6
    @8
    @2
    f1of
    syl
    cS
    cB
    snssi
    fssd
    @7
    @6
    cB
    @2
    @10
    @7
    @6
    wceq
    0z
    cc0
    fzsn
    ax-mp
    feq2i
    sylibr
    gsumval2
    @0
    cS
    @3
    @2
    cc0
    0z
    @10
    @0
    cc0
    @2
    cfv
    cS
    wceq
    0z
    cc0
    cS
    cz
    cB
    fvsng
    mpan
    seq1i
    3eqtrd
end
