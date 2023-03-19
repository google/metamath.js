include "cseq.mm"
include "cfv.mm"
include "csn.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "fvex.mm"
include "elsn.mm"
include "sylibr.mm"
include "ovex.mm"
include "elsni.mm"
include "oveqan12d.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "seqcl.mm"
include "syl.mm"

theorem seqid3
  let wph: wff ph
  let vx: setvar x
  let c.pl: class .+
  let cF: class F
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vy: setvar y
  assume seqid3.1: |- ( ph -> ( Z .+ Z ) = Z )
  assume seqid3.2: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume seqid3.3: |- ( ( ph /\ x e. ( M ... N ) ) -> ( F ` x ) = Z )

  disjoint .+ x
  disjoint F x
  disjoint M x
  disjoint ph x
  disjoint Z x
  disjoint N x
  disjoint x y
  disjoint .+ y
  disjoint F y
  disjoint M y
  disjoint ph y
  disjoint Z y
  assert |- ( ph -> ( seq M ( .+ , F ) ` N ) = Z )

  proof
    wph
    cN
    c.pl
    cF
    cM
    cseq
    cfv
    #
    cZ
    csn
    #
    wcel
    @0
    cZ
    wceq
    wph
    vx
    vy
    c.pl
    @1
    cF
    cM
    cN
    seqid3.2
    wph
    vx
    cv
    #
    cM
    cN
    cfz
    co
    wcel
    wa
    @2
    cF
    cfv
    #
    cZ
    wceq
    @3
    @1
    wcel
    seqid3.3
    @3
    cZ
    @2
    cF
    fvex
    elsn
    sylibr
    wph
    @2
    @1
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    wa
    #
    @2
    @5
    c.pl
    co
    #
    @1
    wcel
    #
    wph
    @9
    @7
    cZ
    cZ
    c.pl
    co
    #
    @1
    wcel
    #
    wph
    @10
    cZ
    wceq
    @11
    seqid3.1
    @10
    cZ
    cZ
    cZ
    c.pl
    ovex
    elsn
    sylibr
    @7
    @8
    @10
    @1
    @4
    @6
    @2
    cZ
    @5
    cZ
    c.pl
    @2
    cZ
    elsni
    @5
    cZ
    elsni
    oveqan12d
    eleq1d
    syl5ibrcom
    imp
    seqcl
    @0
    cZ
    elsni
    syl
end
